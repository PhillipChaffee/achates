//! `achates equiv`: for each C function of the selection that has a Rust
//! counterpart in the Aeneas output, the Lean theorem that the two are
//! equal, and the search for its proof by fixed tactic tiers: each
//! theorem starts at the tier its shape predicts, gets at most two tries,
//! and the outcome is cached under a key of everything it depends on.
//!
//! The pairing is by name only: mpv's `misc/x.c` (or `x.h`) becomes the
//! port's module `x`, and the C function's name in snake case its name
//! there, as the port's conventions say. A function the rule does not find
//! is reported, never guessed.

mod cache;
mod lean;
mod prove;
mod search;
mod sha256;
mod shape;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result};
use serde::Serialize;
use serde_json::Value;

use crate::compdb::Entry;
use crate::frontend;
use cache::TryRecord;
use lean::Def;
use prove::{Goal, Job, Tier, Try};
use search::{Args, Failure, Next, Reach};
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
    /// Search for the proofs; otherwise only write the statements.
    pub(crate) prove: bool,
    pub(crate) jobs: usize,
    /// Do not read `tiers.json`: search every theorem.
    pub(crate) no_cache: bool,
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
    /// The tries behind the outcome, in order.
    tries: Vec<TryRecord>,
    /// The outcome is the cache's: nothing was run for it this time.
    cached: bool,
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

/// What a pair reaches on each side, and what follows from it.
struct Reached {
    c: BTreeSet<String>,
    r: BTreeSet<String>,
    reach: Reach,
    /// The digest of every definition reached, for the cache key.
    sources: String,
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

    /// What the C definition `c` and the Rust one `rust` reach.
    fn reached(&self, c: &str, rust: &str) -> Reached {
        let c_reach = lean::reach(&self.c_defs, c, &[]);
        let r_reach = lean::reach(&self.r_defs, rust, &[self.r_prefix.as_str()]);
        let c_bodies = || c_reach.iter().filter_map(|n| self.c_defs.get(n));
        let r_bodies = || r_reach.iter().filter_map(|n| self.r_defs.get(n));
        let reach = Reach {
            c_loops: c_bodies().any(|d| d.recursive() || d.body.contains("Fuel.mk")),
            reads_statics: c_bodies().any(|d| d.body.contains("Statics.")),
            axioms: r_reach
                .iter()
                .filter(|n| self.r_defs.get(*n).is_some_and(|d| d.axiom))
                .cloned()
                .collect(),
            branches: c_bodies().chain(r_bodies()).any(Def::branches),
            args: Args::Scalars,
        };
        // What the result depends on, of the two generated sides: every
        // definition either side reaches and, for a theorem that assumes
        // `StaticsReady`, what `Statics.init` builds.
        let mut c_deps = c_reach.clone();
        if reach.reads_statics {
            c_deps.extend(lean::reach(&self.c_defs, STATICS_INIT, &[]));
        }
        let sources = sha256::hex(
            format!(
                "{}\n{}",
                cache::defs_digest(&self.c_defs, &c_deps),
                cache::defs_digest(&self.r_defs, &r_reach)
            )
            .as_bytes(),
        );
        Reached {
            c: c_reach,
            r: r_reach,
            reach,
            sources,
        }
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
            tries: vec![],
            cached: false,
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
        let Reached {
            c: c_reach,
            r: r_reach,
            mut reach,
            sources,
        } = self.reached(&lean_name, &rust);
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
                reach.args = if st.bstr_arg {
                    Args::Bstrs
                } else if st.cstr_arg {
                    Args::CStrings
                } else {
                    Args::Scalars
                };
                row.shape = Some(st.shape);
                row.preconditions = st.preconditions;
                // Recursive definitions are left folded: unfolding one does
                // not terminate.
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
                    sources,
                };
                (row, Some((goal, reach)))
            }
        }
    }
}

/// The definition that builds the static objects, which `StaticsReady`
/// names.
const STATICS_INIT: &str = "Misc.Statics.init";

pub(crate) fn run(entries: &[&Entry], opts: &Options) -> Result<String> {
    let status: Vec<Value> = serde_json::from_str(
        &std::fs::read_to_string(opts.c_project.join("status.json"))
            .context("reading status.json")?,
    )?;
    let sides = Sides::load(entries, opts)?;
    let mut rows = Vec::new();
    let mut goals = Vec::new();
    let mut reach = Vec::new();
    for e in &status {
        let (row, goal) = sides.pair(e);
        rows.push(row);
        if let Some((g, r)) = goal {
            goals.push(g);
            reach.push(r);
        }
    }
    let tiers = search::tiers();
    let outcomes = if opts.prove {
        Some(search_all(opts, &goals, &reach, &tiers)?)
    } else {
        None
    };
    write_outputs(opts, &goals, &tiers, outcomes.as_ref(), &mut rows)?;
    Ok(summary(&rows, &tiers))
}

/// What became of one theorem in a run.
#[derive(Debug, Clone)]
struct Outcome {
    entry: cache::Entry,
    cached: bool,
}

/// `lean --version`, as `lake env` finds it in `lake_dir`.
fn toolchain(lake_dir: &Path) -> Result<String> {
    let out = std::process::Command::new("lake")
        .args(["env", "lean", "--version"])
        .current_dir(lake_dir)
        .output()
        .context("running lake env lean --version (is Lean on PATH?)")?;
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_owned())
}

/// The cache's record of one try.
fn record(t: &Try) -> TryRecord {
    let result = match &t.failure {
        None => "proved".to_owned(),
        Some(Failure::Budget { at }) => format!("out of heartbeats at `{at}`"),
        Some(Failure::Unsolved(_)) => "unsolved goals".to_owned(),
        Some(Failure::Script(line)) => format!("script step failed: {line}"),
        Some(Failure::Axioms(a)) => format!("axioms not Lean's own: {a}"),
        Some(Failure::Stopped(why)) => format!("stopped: {why}"),
    };
    TryRecord {
        tier: t.tier,
        budget: t.budget,
        heartbeats: t.heartbeats,
        seconds: (t.seconds * 10.0).round() / 10.0,
        result,
        first_error: (!t.first_error.is_empty()).then(|| t.first_error.clone()),
    }
}

/// After a theorem's tries so far, the tier of the next, if it gets one:
/// never after a proof, never a third, and only where the failure points
/// to a tier that has what the theorem lacks.
fn next_tier(tries: &[Try], r: &Reach) -> Option<usize> {
    let last = tries.last()?;
    let failure = last.failure.as_ref()?;
    if tries.len() >= search::TRIES {
        return None;
    }
    match search::decide(last.tier, failure, r) {
        Next::Tier(t) => Some(t),
        Next::Stop(_) => None,
    }
}

/// Why a theorem is open after `tries`.
fn open_reason(tries: &[Try], r: &Reach, tiers: &[Tier]) -> String {
    let Some((last, failure)) = tries.last().and_then(|t| Some((t, t.failure.as_ref()?))) else {
        return String::new();
    };
    match search::decide(last.tier, failure, r) {
        Next::Stop(why) => why,
        Next::Tier(t) => format!(
            "{} tries made; {} would be next",
            tries.len(),
            tiers.get(t).map_or("another tier", |t| t.label.as_str())
        ),
    }
}

/// The search: theorems whose cache entry holds for their key now are
/// not run; the rest start at their predicted tier, the longest expected
/// first.
fn search_all(
    opts: &Options,
    goals: &[Goal],
    reach: &[Reach],
    tiers: &[Tier],
) -> Result<Vec<Outcome>> {
    prove::build_imports(&opts.lake_dir)?;
    let cache_path = opts.lake_dir.join("tiers.json");
    let old = if opts.no_cache {
        cache::Cache::default()
    } else {
        cache::load(&cache_path)
    };
    let global = cache::global_key(&opts.lake_dir, tiers, &toolchain(&opts.lake_dir)?)?;
    let keys: Vec<String> = goals.iter().map(|g| cache::key(&global, g)).collect();
    let mut out: Vec<Option<Outcome>> = vec![None; goals.len()];
    let mut first = Vec::new();
    for (i, (g, k)) in goals.iter().zip(&keys).enumerate() {
        let entry = old.theorems.get(&g.name);
        if let (Some(e), Some(slot)) = (entry.filter(|e| &e.key == k), out.get_mut(i)) {
            *slot = Some(Outcome {
                entry: e.clone(),
                cached: true,
            });
            continue;
        }
        let tier = reach.get(i).map_or(0, search::predict);
        // A stale entry's time still estimates the cost; a theorem with
        // none goes first, as possibly the longest.
        let cost = entry.map_or(f64::INFINITY, cache::Entry::seconds);
        first.push((cost, Job { goal: i, tier }));
    }
    first.sort_by(|a, b| b.0.total_cmp(&a.0));
    let first: Vec<Job> = first.into_iter().map(|(_, j)| j).collect();
    eprintln!(
        "achates equiv: {} theorems, {} from the cache, {} to search",
        goals.len(),
        goals.len() - first.len(),
        first.len()
    );
    let work = opts.lake_dir.join("attempts");
    if let Ok(dir) = std::fs::read_dir(&work) {
        for e in dir.flatten() {
            if e.path().extension().is_some_and(|x| x == "lean") {
                let _ = std::fs::remove_file(e.path());
            }
        }
    }
    let next = |g: usize, tries: &[Try]| next_tier(tries, reach.get(g)?);
    let tries = prove::run(
        goals,
        tiers,
        &first,
        &next,
        &opts.lake_dir,
        &work,
        opts.jobs,
    )?;
    let mut new_cache = cache::Cache::default();
    for (i, g) in goals.iter().enumerate() {
        let (Some(slot), Some(k)) = (out.get_mut(i), keys.get(i)) else {
            continue;
        };
        if slot.is_none() {
            let ts = tries.get(i).map(Vec::as_slice).unwrap_or_default();
            let proved = ts.last().filter(|t| t.failure.is_none());
            let r = reach.get(i).cloned().unwrap_or_default();
            *slot = Some(Outcome {
                entry: cache::Entry {
                    key: k.clone(),
                    proved: proved.map(|t| t.tier),
                    reason: proved.is_none().then(|| open_reason(ts, &r, tiers)),
                    tries: ts.iter().map(record).collect(),
                    axioms: proved.and_then(|t| t.axioms.clone()),
                },
                cached: false,
            });
        }
        // A Lean run that stopped says nothing about the theorem: it is
        // not kept, so the next run searches it again.
        let stopped = tries
            .get(i)
            .and_then(|ts| ts.last())
            .is_some_and(|t| matches!(t.failure, Some(Failure::Stopped(_))));
        if let Some(o) = slot
            && !stopped
        {
            new_cache.theorems.insert(g.name.clone(), o.entry.clone());
        }
    }
    cache::save(&cache_path, &new_cache)?;
    Ok(out.into_iter().flatten().collect())
}

/// The budget line and the statement with `tier`'s script.
fn with_budget(goal: &Goal, tier: &Tier) -> String {
    format!(
        "set_option maxHeartbeats {} in\n{}",
        tier.budget,
        prove::proof(goal, tier)
    )
}

fn write_outputs(
    opts: &Options,
    goals: &[Goal],
    tiers: &[Tier],
    outcomes: Option<&Vec<Outcome>>,
    rows: &mut [Row],
) -> Result<()> {
    let mut proved = String::from(prove::HEADER);
    let mut checks = String::new();
    let mut open = String::from(
        "/-! The generated theorems no tier proved, each with the script of its\n\
         last try and that try's first error. This file is not built. -/\n\n",
    );
    open.push_str(prove::HEADER);
    let fallback = Tier {
        label: String::new(),
        tactic: "skip".to_owned(),
        budget: 0,
    };
    for (i, g) in goals.iter().enumerate() {
        let o = outcomes.and_then(|o| o.get(i));
        let row = rows
            .iter_mut()
            .find(|r| r.c == g.name && r.status == "generated");
        if let Some((t, o)) = o.and_then(|o| Some((o.entry.proved?, o))) {
            let tier = tiers.get(t).unwrap_or(&fallback);
            let _ = writeln!(proved, "{}", with_budget(g, tier));
            // The build checks the axioms too: the message must be the one
            // the run accepted, which named only Lean's own. The checks go
            // after every theorem: `#print axioms` waits for the proof, and
            // in between it would stop the theorems from being checked in
            // parallel.
            if let Some(ax) = &o.entry.axioms {
                let _ = writeln!(
                    checks,
                    "/-- info: {ax} -/\n#guard_msgs (whitespace := lax) in\n#print axioms Equiv.Gen.{}\n",
                    g.name
                );
            }
            if let Some(r) = row {
                r.proved = Some(tier.label.clone());
                r.tries.clone_from(&o.entry.tries);
                r.cached = o.cached;
            }
        } else {
            let last = o.and_then(|o| o.entry.tries.last());
            let tier = last
                .and_then(|t| tiers.get(t.tier))
                .or_else(|| tiers.first())
                .unwrap_or(&fallback);
            let err = last.and_then(|t| t.first_error.clone()).unwrap_or_default();
            let _ = writeln!(open, "/- First error of {}:\n{err}-/", tier.label);
            let _ = writeln!(open, "{}", with_budget(g, tier));
            if let (Some(r), Some(o)) = (row, o) {
                r.open_reason.clone_from(&o.entry.reason);
                r.first_error = Some(err);
                r.tries.clone_from(&o.entry.tries);
                r.cached = o.cached;
            }
        }
    }
    for r in rows.iter_mut() {
        for t in &mut r.tries {
            t.first_error = None;
        }
    }
    proved.push_str(&checks);
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

/// How a row's outcome was reached, for the summary: the tiers tried and
/// whether the cache supplied it.
fn tried(r: &Row) -> String {
    let tiers: Vec<String> = r.tries.iter().map(|t| t.tier.to_string()).collect();
    let n = r.tries.len();
    format!(
        "{n} {} (tier {}){}",
        if n == 1 { "try" } else { "tries" },
        tiers.join(", then "),
        if r.cached { ", cached" } else { "" }
    )
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
    let fresh = || rows.iter().filter(|r| !r.cached);
    let _ = writeln!(
        s,
        "outcomes from the cache, not run again: {}",
        count(&|r| r.cached)
    );
    let _ = writeln!(
        s,
        "tries this run: {} ({} theorems with one, {} with two)",
        fresh().map(|r| r.tries.len()).sum::<usize>(),
        fresh().filter(|r| r.tries.len() == 1).count(),
        fresh().filter(|r| r.tries.len() == 2).count()
    );
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
                .map(|p| format!(", proved at {p}, {}", tried(r)))
                .or_else(|| r
                    .open_reason
                    .as_ref()
                    .map(|o| format!(", open after {}: {o}", tried(r))))
                .unwrap_or_default()
        );
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn failed(tier: usize, failure: Failure) -> Try {
        Try {
            tier,
            budget: 1,
            heartbeats: None,
            seconds: 1.0,
            failure: Some(failure),
            first_error: "e".into(),
            axioms: None,
        }
    }

    #[test]
    fn a_theorem_gets_at_most_two_tries() {
        let r = Reach {
            args: Args::Bstrs,
            branches: true,
            ..Reach::default()
        };
        let branch = Failure::Unsolved(search::Residual {
            branch: true,
            ..search::Residual::default()
        });
        let memory = Failure::Unsolved(search::Residual {
            memory: search::Left::Memory,
            ..search::Residual::default()
        });
        // An `if` left at tier 0 points to tier 1.
        let one = [failed(0, branch.clone())];
        assert_eq!(next_tier(&one, &r), Some(1));
        // Memory left at tier 1 points to tier 2, but that would be a
        // third try.
        let two = [failed(0, branch), failed(1, memory.clone())];
        assert_eq!(search::decide(1, &memory, &r), Next::Tier(2));
        assert_eq!(next_tier(&two, &r), None);
        let tiers = search::tiers();
        assert_eq!(
            open_reason(&two, &r, &tiers),
            "2 tries made; tier 2 would be next"
        );
        // A proof ends the search.
        let mut proved = failed(2, memory);
        proved.failure = None;
        assert_eq!(next_tier(&[proved], &r), None);
    }

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
