//! `achates equiv`: for each C function of the selection that has a Rust
//! counterpart in the Aeneas output, the Lean theorem that the two are
//! equal, and the attempt to prove it by fixed tactic tiers.
//!
//! The pairing is by name only: mpv's `misc/x.c` (or `x.h`) becomes the
//! port's module `x`, and the C function's name in snake case its name
//! there, as the port's conventions say. A function the rule does not find
//! is reported, never guessed.

mod lean;
mod prove;
mod shape;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result};
use serde::Serialize;
use serde_json::Value;

use crate::compdb::Entry;
use crate::frontend;
use lean::Def;
use prove::{Goal, Outcome, Tier};
use shape::Proto;

#[derive(Debug)]
pub(crate) struct Options {
    /// The emitted C project (`status.json` and the `.lean` files).
    pub(crate) c_project: PathBuf,
    /// The Lean file Aeneas wrote.
    pub(crate) rust_lean: PathBuf,
    /// The bridge Lake project: theorems are written into it and checked
    /// with its `lake env`.
    pub(crate) lake_dir: PathBuf,
    /// Attempt the proofs; otherwise only write the statements.
    pub(crate) prove: bool,
    pub(crate) jobs: usize,
}

/// The tiers in the order they are tried.
///
/// Each has its own heartbeat budget, the most a try at that tier is
/// allowed, set from measurement (`docs/equiv-report.md`, "Budgets"), in
/// the units of `maxHeartbeats` (about 12,000 to the second per Lean
/// process on the machine measured, four at a time):
///
/// * tier 0, 400 thousand (about 30 s): its one proof needs 316, and a
///   theorem it runs out on goes to tier 1, which splits;
/// * tier 1, 8 million (about 11 min): the largest proof measured,
///   `h_to_i`, needs 4.2 million;
/// * tier 2, 4 million (about 5 min): its proofs need at most 262
///   thousand, no theorem that ran out closed with several times more, and
///   three of them grew past 5 GB before twice this, too much for four
///   tries at once on 16 GB.
fn tiers() -> Vec<Tier> {
    let t = |label: &str, tactic: &str, budget: u64| Tier {
        label: label.to_owned(),
        tactic: tactic.to_owned(),
        budget,
    };
    vec![
        t("tier 0", "equiv_tier0 [UNFOLD]", 400_000),
        t("tier 1", "equiv_tier1 [UNFOLD]", 8_000_000),
        t("tier 2", "equiv_tier2 [UNFOLD]", 4_000_000),
    ]
}

/// The budget line and the statement with `tier`'s script.
fn with_budget(goal: &Goal, tier: &Tier) -> String {
    format!(
        "set_option maxHeartbeats {} in\n{}",
        tier.budget,
        prove::proof(goal, tier)
    )
}

/// What became of one C function.
#[derive(Debug, Serialize)]
struct Row {
    c: String,
    file: String,
    rust: Option<String>,
    /// `generated`, or why not.
    status: String,
    shape: Option<String>,
    preconditions: Vec<String>,
    /// The C side's named assumptions, from `status.json`.
    assumptions: Vec<String>,
    /// Axioms the Rust side reaches.
    rust_axioms: Vec<String>,
    proved: Option<String>,
    open_reason: Option<String>,
    first_error: Option<String>,
}

fn snake(name: &str) -> String {
    let mut s = String::new();
    let mut prev_lower = false;
    for c in name.chars() {
        if c.is_ascii_uppercase() {
            if prev_lower {
                s.push('_');
            }
            s.push(c.to_ascii_lowercase());
            prev_lower = false;
        } else {
            prev_lower = c.is_ascii_lowercase() || c.is_ascii_digit();
            s.push(c);
        }
    }
    s
}

fn stem(file: &str) -> String {
    let base = file.rsplit('/').next().unwrap_or(file);
    let stem = base.split('.').next().unwrap_or(base);
    stem.replace('-', "_")
}

fn lean_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    for e in std::fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let p = e?.path();
        if p.is_dir() {
            lean_files(&p, out)?;
        } else if p.extension().is_some_and(|x| x == "lean") {
            out.push(p);
        }
    }
    Ok(())
}

fn defs_of(files: &[PathBuf]) -> Result<BTreeMap<String, Def>> {
    let mut m = BTreeMap::new();
    for f in files {
        let text =
            std::fs::read_to_string(f).with_context(|| format!("reading {}", f.display()))?;
        for d in lean::parse(&text) {
            m.insert(d.name.clone(), d);
        }
    }
    Ok(m)
}

/// The C prototypes of the selection, by (file name, function name).
fn protos(entries: &[&Entry]) -> Result<BTreeMap<(String, String), Proto>> {
    let mut out = BTreeMap::new();
    for e in entries {
        let loaded = frontend::load(e, true)?;
        for f in &loaded.tu.functions {
            let base = f
                .def_file
                .rsplit('/')
                .next()
                .unwrap_or(&f.def_file)
                .to_owned();
            out.entry((base, f.name.clone())).or_insert_with(|| Proto {
                params: f.params.iter().map(|p| p.ty.to_string()).collect(),
                ret: f.ret.to_string(),
            });
        }
    }
    Ok(out)
}

/// What both sides reach, for sorting the open theorems.
#[derive(Debug, Clone, Default)]
struct Reach {
    c_loops: bool,
    reads_statics: bool,
    scalar_only: bool,
    axioms: Vec<String>,
}

/// Why an open theorem is open, from the first error of its most
/// informative attempt and what both sides reach. A first sorting, checked
/// by hand in the report.
fn classify(error: &str, r: &Reach) -> String {
    if !r.axioms.is_empty() {
        return "Aeneas axiom reached".to_owned();
    }
    if error.contains("counterexample") && !error.contains("potentially spurious") {
        return "possible mismatch: bv_decide found a counterexample".to_owned();
    }
    if r.c_loops {
        return "loop: a C loop needs a fuel bound and an invariant".to_owned();
    }
    if error.contains("_loop") {
        return "loop: a Rust recursion needs an induction".to_owned();
    }
    if r.reads_statics {
        return "memory: static tables against Aeneas constants".to_owned();
    }
    if error.contains("StateT.run") || error.contains("Mem.") || error.contains("IsBstr") {
        return "memory correspondence".to_owned();
    }
    "arithmetic or unfolding".to_owned()
}

fn strings(e: &Value, key: &str) -> Vec<String> {
    e.get(key)
        .and_then(Value::as_array)
        .map(|a| {
            a.iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

/// Both sides, loaded once.
struct Sides {
    c_defs: BTreeMap<String, Def>,
    r_defs: BTreeMap<String, Def>,
    protos: BTreeMap<(String, String), Proto>,
    r_prefix: String,
}

impl Sides {
    fn load(entries: &[&Entry], opts: &Options) -> Result<Self> {
        let mut c_files = Vec::new();
        lean_files(&opts.c_project.join("Misc"), &mut c_files)?;
        let r_defs = defs_of(std::slice::from_ref(&opts.rust_lean))?;
        let r_prefix = r_defs
            .keys()
            .next()
            .and_then(|k| k.split('.').next())
            .unwrap_or("rmpv_misc")
            .to_owned();
        Ok(Self {
            c_defs: defs_of(&c_files)?,
            r_defs,
            protos: protos(entries)?,
            r_prefix,
        })
    }

    /// Why `rust` is not a Rust function to pair with, if it is not.
    fn unmatched(&self, rust: &str, c_name: &str) -> Option<String> {
        if self.r_defs.get(rust).is_some_and(|d| !d.axiom) {
            return None;
        }
        Some(if self.r_defs.get(rust).is_some_and(|d| d.axiom) {
            format!("not generated: `{rust}` is an Aeneas declaration without a body")
        } else if let Some(other) = self
            .r_defs
            .keys()
            .find(|k| k.ends_with(&format!(".{}", snake(c_name))))
        {
            format!("not matched: naming rule gives `{rust}`, but `{other}` exists")
        } else {
            format!("not matched: no `{rust}` in the Aeneas output")
        })
    }

    /// The row of one `status.json` entry, and its goal if a template applies.
    fn pair(&self, e: &Value) -> (Row, Option<(Goal, Reach)>) {
        let get = |k: &str| e.get(k).and_then(Value::as_str).unwrap_or("").to_owned();
        let (c_name, file, lean_name) = (get("function"), get("file"), get("lean"));
        let rust = format!("{}.{}.{}", self.r_prefix, stem(&file), snake(&c_name));
        let mut row = Row {
            c: c_name.clone(),
            file: file.clone(),
            rust: None,
            status: String::new(),
            shape: None,
            preconditions: vec![],
            assumptions: strings(e, "assumptions")
                .iter()
                .map(|s| s.split(':').next().unwrap_or(s).to_owned())
                .collect(),
            rust_axioms: vec![],
            proved: None,
            open_reason: None,
            first_error: None,
        };
        if let Some(why) = self.unmatched(&rust, &c_name) {
            row.status = why;
            return (row, None);
        }
        row.rust = Some(rust.clone());
        let externals = strings(e, "externals");
        let base = file.rsplit('/').next().unwrap_or(&file).to_owned();
        let found = (
            self.c_defs.get(&lean_name),
            self.protos.get(&(base, c_name)),
            self.r_defs.get(&rust),
        );
        let (Some(c_def), Some(proto), Some(r_def)) = found else {
            row.status = if get("status") == "emitted" {
                "not generated: C definition or prototype not found".to_owned()
            } else {
                "not generated: the C side is not emitted".to_owned()
            };
            return (row, None);
        };
        if !externals.is_empty() {
            row.status = format!(
                "not generated: the C side takes external functions as parameters ({})",
                externals.join(", ")
            );
            return (row, None);
        }
        let c_reach = lean::reach(&self.c_defs, &lean_name, &[]);
        let r_reach = lean::reach(&self.r_defs, &rust, &[self.r_prefix.as_str()]);
        let c_bodies = || c_reach.iter().filter_map(|n| self.c_defs.get(n));
        let mut reach = Reach {
            c_loops: c_bodies().any(|d| d.recursive() || d.body.contains("Fuel.mk")),
            reads_statics: c_bodies().any(|d| d.body.contains("Statics.")),
            scalar_only: false,
            axioms: r_reach
                .iter()
                .filter(|n| self.r_defs.get(*n).is_some_and(|d| d.axiom))
                .cloned()
                .collect(),
        };
        row.rust_axioms.clone_from(&reach.axioms);
        let thm = lean_name
            .rsplit('.')
            .next()
            .unwrap_or(&lean_name)
            .to_owned();
        match shape::statement(&thm, c_def, proto, r_def, reach.reads_statics, "TACTIC") {
            Err(why) => {
                row.status = format!("no template yet: {why}");
                (row, None)
            }
            Ok(st) => {
                "generated".clone_into(&mut row.status);
                reach.scalar_only = st.shape.starts_with("scalar arguments");
                row.shape = Some(st.shape);
                row.preconditions = st.preconditions;
                // Recursive definitions are left folded: unfolding one does
                // not terminate. Loops are tier 2's business.
                let c_unfold = c_reach
                    .iter()
                    .filter(|n| self.c_defs.get(*n).is_some_and(|d| !d.recursive()));
                let r_unfold = r_reach.iter().filter(|n| {
                    self.r_defs
                        .get(*n)
                        .is_some_and(|d| !d.recursive() && !d.axiom)
                });
                let unfold: BTreeSet<String> = c_unfold.chain(r_unfold).cloned().collect();
                let goal = Goal {
                    name: thm,
                    text: st.text,
                    unfold: unfold.into_iter().collect(),
                };
                (row, Some((goal, reach)))
            }
        }
    }
}

pub(crate) fn run(entries: &[&Entry], opts: &Options) -> Result<String> {
    let status: Vec<Value> = serde_json::from_str(
        &std::fs::read_to_string(opts.c_project.join("status.json"))
            .context("reading status.json")?,
    )?;
    let sides = Sides::load(entries, opts)?;
    let mut rows = Vec::new();
    let mut goals = Vec::new();
    let mut meta: BTreeMap<String, Reach> = BTreeMap::new();
    for e in &status {
        let (row, goal) = sides.pair(e);
        rows.push(row);
        if let Some((g, reach)) = goal {
            meta.insert(g.name.clone(), reach);
            goals.push(g);
        }
    }
    let tiers = tiers();
    let outcomes: BTreeMap<String, Outcome> = if opts.prove {
        prove::run(
            &goals,
            &tiers,
            &opts.lake_dir,
            &opts.lake_dir.join("attempts"),
            opts.jobs,
        )?
    } else {
        BTreeMap::new()
    };
    write_outputs(opts, &goals, &tiers, &outcomes, &mut rows, &meta)?;
    Ok(summary(&rows, &tiers))
}

fn write_outputs(
    opts: &Options,
    goals: &[Goal],
    tiers: &[Tier],
    outcomes: &BTreeMap<String, Outcome>,
    rows: &mut [Row],
    meta: &BTreeMap<String, Reach>,
) -> Result<()> {
    let mut proved = String::from(prove::HEADER);
    let mut open = String::from(
        "/-! The generated theorems no tier proved, each with the tactic of the last\n\
         tier tried and that tier's first error. This file is not built. -/\n\n",
    );
    open.push_str(prove::HEADER);
    let last = tiers.last().cloned().unwrap_or_else(|| Tier {
        label: String::new(),
        tactic: "skip".to_owned(),
        budget: 0,
    });
    for g in goals {
        let o = outcomes.get(&g.name);
        let row = rows
            .iter_mut()
            .find(|r| r.c == g.name && r.status == "generated");
        if let Some(t) = o.and_then(|o| o.proved) {
            let tier = tiers.get(t).cloned().unwrap_or_else(|| last.clone());
            let _ = writeln!(proved, "{}", with_budget(g, &tier));
            if let Some(r) = row {
                r.proved = Some(tier.label);
            }
        } else {
            // The attempt that got furthest says most about why a
            // theorem is open: tier 1 for scalars, whose tier 2 stops at
            // once, and the last tier for memory.
            let reach = meta.get(&g.name).cloned().unwrap_or_default();
            let pick = if reach.scalar_only {
                1
            } else {
                tiers.len().saturating_sub(1)
            };
            let generic = tiers.get(pick).cloned().unwrap_or_else(|| last.clone());
            let err = o
                .and_then(|o| {
                    o.errors
                        .iter()
                        .find(|(t, _)| *t == pick)
                        .or_else(|| o.errors.last())
                })
                .map(|(_, e)| e.clone())
                .unwrap_or_default();
            let _ = writeln!(
                open,
                "/- First error of {}:\n{}-/",
                generic.label,
                prove::summary(&err)
            );
            let _ = writeln!(open, "{}", with_budget(g, &generic));
            if let Some(r) = row
                && opts.prove
            {
                r.open_reason = Some(classify(&err, &reach));
                r.first_error = Some(prove::summary(&err));
            }
        }
    }
    proved.push_str("end Equiv.Gen\n");
    open.push_str("end Equiv.Gen\n");
    if opts.prove {
        std::fs::write(opts.lake_dir.join("Equiv/Proved.lean"), proved)?;
    }
    std::fs::create_dir_all(opts.lake_dir.join("open"))?;
    std::fs::write(opts.lake_dir.join("open/Open.lean"), open)?;
    std::fs::write(
        opts.lake_dir.join("results.json"),
        serde_json::to_string_pretty(&rows)? + "\n",
    )?;
    Ok(())
}

fn summary(rows: &[Row], tiers: &[Tier]) -> String {
    let mut s = String::new();
    let count = |f: &dyn Fn(&Row) -> bool| rows.iter().filter(|r| f(r)).count();
    let _ = writeln!(
        s,
        "C functions (selection and header helpers): {}",
        rows.len()
    );
    let _ = writeln!(
        s,
        "paired with a Rust function: {}",
        count(&|r| r.rust.is_some())
    );
    let _ = writeln!(
        s,
        "theorems generated: {}",
        count(&|r| r.status == "generated")
    );
    let mut by: BTreeMap<String, usize> = BTreeMap::new();
    for r in rows {
        let key = r.shape.as_ref().map_or_else(
            || {
                let st = &r.status;
                let cut = st.find(" (").or_else(|| st.find(": `")).unwrap_or(st.len());
                st.get(..cut).unwrap_or(st).to_owned()
            },
            |sh| format!("generated: {sh}"),
        );
        *by.entry(key).or_default() += 1;
    }
    for (k, n) in &by {
        let _ = writeln!(s, "  {n:>3}  {k}");
    }
    for t in tiers {
        let _ = writeln!(
            s,
            "proved at {}: {}",
            t.label,
            count(&|r| r.proved.as_deref() == Some(t.label.as_str()))
        );
    }
    let mut open: BTreeMap<String, usize> = BTreeMap::new();
    for r in rows {
        if let Some(o) = &r.open_reason {
            *open.entry(o.clone()).or_default() += 1;
        }
    }
    for (k, n) in &open {
        let _ = writeln!(s, "open: {n:>3}  {k}");
    }
    let _ = writeln!(s);
    for r in rows {
        let _ = writeln!(
            s,
            "{} -> {}: {}{}",
            r.c,
            r.rust.as_deref().unwrap_or("-"),
            r.status,
            r.proved
                .as_ref()
                .map(|p| format!(", proved at {p}"))
                .or_else(|| r.open_reason.as_ref().map(|o| format!(", open: {o}")))
                .unwrap_or_default()
        );
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_naming_rule() {
        assert_eq!(snake("ucdLookup"), "ucd_lookup");
        assert_eq!(snake("ucdToCharacterWidth"), "ucd_to_character_width");
        assert_eq!(snake("bstr_find"), "bstr_find");
        assert_eq!(snake("mp_rand_next"), "mp_rand_next");
        assert_eq!(stem("../.mpv/misc/bstr.h"), "bstr");
        assert_eq!(stem("../.mpv/osdep/threads-posix.h"), "threads_posix");
    }
}
