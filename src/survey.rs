//! `achates survey`: which functions are fully represented.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use anyhow::Result;

use crate::compdb::Entry;
use crate::frontend;
use crate::scan;

#[derive(Debug, Clone)]
pub(crate) struct FunctionRow {
    pub(crate) file: String,
    pub(crate) name: String,
    pub(crate) lines: u64,
    /// Occurrences of each unrepresented construct, keyed by clang kind and
    /// reason; empty means fully represented.
    pub(crate) counts: BTreeMap<(String, String), usize>,
    pub(crate) builtins: BTreeSet<String>,
}

#[derive(Debug, Default)]
pub(crate) struct Survey {
    pub(crate) rows: Vec<FunctionRow>,
    pub(crate) stripped: BTreeMap<String, Vec<String>>,
}

pub(crate) fn run(entries: &[&Entry]) -> Result<Survey> {
    let mut s = Survey::default();
    for e in entries {
        let loaded = frontend::load(e)?;
        s.stripped.insert(e.file.clone(), loaded.stripped);
        for f in &loaded.tu.functions {
            let all = scan::unsupported_of(f, &loaded.tu);
            let mut counts: BTreeMap<(String, String), usize> = BTreeMap::new();
            for u in &all {
                *counts
                    .entry((u.clang_kind.clone(), u.reason.clone()))
                    .or_default() += 1;
            }
            s.rows.push(FunctionRow {
                file: e.file.clone(),
                name: f.name.clone(),
                lines: f.lines,
                counts,
                builtins: scan::builtins_of(f),
            });
        }
    }
    Ok(s)
}

fn pct(n: usize, d: usize) -> String {
    if d == 0 {
        return "-".into();
    }
    // Integer arithmetic keeps the lints about float casts quiet and is exact.
    let tenths = (n * 1000 + d / 2) / d;
    format!("{}.{}%", tenths / 10, tenths % 10)
}

pub(crate) fn render(s: &Survey) -> String {
    let mut o = String::new();
    let width = s.rows.iter().map(|r| r.name.len()).max().unwrap_or(8);
    for r in &s.rows {
        let status = if r.counts.is_empty() {
            "ok".to_owned()
        } else {
            let parts: Vec<String> = r
                .counts
                .keys()
                .map(|(k, why)| format!("{k}: {why}"))
                .collect();
            format!("UNSUPPORTED {}", parts.join("; "))
        };
        let _ = writeln!(
            o,
            "{}  {:width$}  {:>4} lines  {status}",
            r.file, r.name, r.lines
        );
    }
    o.push('\n');
    let mut files: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    for r in &s.rows {
        let e = files.entry(&r.file).or_default();
        e.0 += 1;
        e.1 += usize::from(r.counts.is_empty());
    }
    for (f, (n, ok)) in &files {
        let _ = writeln!(
            o,
            "{f}: {ok} of {n} functions fully represented ({})",
            pct(*ok, *n)
        );
    }
    let n = s.rows.len();
    let ok = s.rows.iter().filter(|r| r.counts.is_empty()).count();
    let _ = writeln!(
        o,
        "total: {ok} of {n} functions fully represented ({}), in {} files",
        pct(ok, n),
        files.len()
    );
    let mut table: BTreeMap<&(String, String), (usize, usize)> = BTreeMap::new();
    for r in &s.rows {
        for (k, n) in &r.counts {
            let e = table.entry(k).or_default();
            e.0 += 1;
            e.1 += n;
        }
    }
    if !table.is_empty() {
        o.push_str("\nunsupported constructs\nfunctions  occurrences  construct: reason\n");
        let mut rows: Vec<_> = table.into_iter().collect();
        rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));
        for ((k, why), (fns, occ)) in rows {
            let _ = writeln!(o, "{fns:>9}  {occ:>11}  {k}: {why}");
        }
    }
    let mut builtins: BTreeMap<&str, usize> = BTreeMap::new();
    for b in s.rows.iter().flat_map(|r| &r.builtins) {
        *builtins.entry(b).or_default() += 1;
    }
    if !builtins.is_empty() {
        o.push_str("\ncompiler builtins and atomic operations (represented as calls; functions using each)\n");
        for (b, n) in builtins {
            let _ = writeln!(o, "{n:>9}  {b}");
        }
    }
    let gcc_only: BTreeSet<&str> = s
        .stripped
        .values()
        .flatten()
        .map(String::as_str)
        .filter(|a| {
            crate::compdb::GCC_ONLY_FLAGS.contains(a)
                || crate::compdb::GCC_ONLY_PREFIXES
                    .iter()
                    .any(|p| a.starts_with(p))
        })
        .collect();
    if !gcc_only.is_empty() {
        let v: Vec<&str> = gcc_only.into_iter().collect();
        let _ = writeln!(o, "\ngcc-only flags removed: {}", v.join(" "));
    }
    o
}
