//! `achates survey`: which functions are fully represented, which header
//! functions they reach, and which functions they call that the selection
//! does not define.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use anyhow::{Result, bail};

use crate::compdb::Entry;
use crate::frontend;
use crate::ir::Origin;
use crate::{dump, scan};

/// A function's identity across translation units: defining file and name.
pub(crate) type Id = (String, String);

/// Occurrences of each unrepresented construct, keyed by clang kind and
/// reason; empty means fully represented.
pub(crate) type Counts = BTreeMap<(String, String), usize>;

#[derive(Debug, Clone)]
pub(crate) struct FunctionRow {
    pub(crate) file: String,
    pub(crate) name: String,
    pub(crate) lines: u64,
    /// Constructs not represented in the function's own body.
    pub(crate) counts: Counts,
    pub(crate) builtins: BTreeSet<String>,
    /// Header functions the function reaches.
    pub(crate) reaches: Vec<Id>,
}

#[derive(Debug, Clone)]
pub(crate) struct HeaderRow {
    pub(crate) origin: Origin,
    pub(crate) lines: u64,
    pub(crate) counts: Counts,
    fingerprint: String,
    first_unit: String,
    /// Places where selected functions name it.
    pub(crate) sites_from_selected: usize,
    /// Places where other header functions name it.
    pub(crate) sites_from_headers: usize,
    /// Selected functions that reach it, directly or through other headers.
    pub(crate) reached_by: usize,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct External {
    pub(crate) selected_callers: BTreeSet<Id>,
    pub(crate) header_callers: BTreeSet<Id>,
    pub(crate) sites: usize,
}

#[derive(Debug, Default)]
pub(crate) struct Survey {
    pub(crate) rows: Vec<FunctionRow>,
    pub(crate) headers: BTreeMap<Id, HeaderRow>,
    /// Functions named but defined nowhere in the selection.
    pub(crate) externals: BTreeMap<String, External>,
    pub(crate) stripped: BTreeMap<String, Vec<String>>,
}

impl Survey {
    /// A selected function whose own body and every header function it
    /// reaches are fully represented.
    pub(crate) fn strictly_ok(&self, r: &FunctionRow) -> bool {
        r.counts.is_empty()
            && r.reaches
                .iter()
                .all(|id| self.headers.get(id).is_some_and(|h| h.counts.is_empty()))
    }
}

fn counts_of(f: &crate::ir::Function, tu: &crate::ir::TranslationUnit) -> Counts {
    let mut counts = Counts::new();
    for u in scan::unsupported_of(f, tu) {
        *counts.entry((u.clang_kind, u.reason)).or_default() += 1;
    }
    counts
}

/// A reference not resolved within its translation unit.
struct Pending {
    callee: String,
    caller: Id,
    from_header: bool,
    sites: usize,
}

/// Adds one translation unit's functions; references it cannot resolve go
/// to `pending`.
fn add_unit(
    s: &mut Survey,
    e: &Entry,
    tu: &crate::ir::TranslationUnit,
    pending: &mut Vec<Pending>,
) -> Result<()> {
    let mut header_ids: BTreeMap<&str, Id> = BTreeMap::new();
    let mut fresh = BTreeSet::new();
    for h in tu.functions.iter().filter(|f| f.origin != Origin::MainFile) {
        let id = (h.def_file.clone(), h.name.clone());
        header_ids.insert(&h.name, id.clone());
        let fingerprint = dump::fingerprint(h);
        if let Some(old) = s.headers.get(&id) {
            if old.fingerprint != fingerprint {
                bail!(
                    "header function `{}` in {} has different bodies in {} and {} (an `#if` \
                     that differs between the two)",
                    id.1,
                    id.0,
                    old.first_unit,
                    e.file
                );
            }
            continue;
        }
        fresh.insert(id.clone());
        s.headers.insert(
            id,
            HeaderRow {
                origin: h.origin,
                lines: h.lines,
                counts: counts_of(h, tu),
                fingerprint,
                first_unit: e.file.clone(),
                sites_from_selected: 0,
                sites_from_headers: 0,
                reached_by: 0,
            },
        );
    }
    for f in &tu.functions {
        let id = (f.def_file.clone(), f.name.clone());
        let from_header = f.origin != Origin::MainFile;
        // A header function's references are counted in the first unit
        // that defines it only, since every unit sees the same body.
        if from_header && !fresh.contains(&id) {
            continue;
        }
        for (callee, n) in scan::refs_of(f) {
            match header_ids
                .get(callee.as_str())
                .and_then(|h| s.headers.get_mut(h))
            {
                Some(h) if from_header => h.sites_from_headers += n,
                Some(h) => h.sites_from_selected += n,
                None => pending.push(Pending {
                    callee,
                    caller: id.clone(),
                    from_header,
                    sites: n,
                }),
            }
        }
        if from_header {
            continue;
        }
        let reaches: Vec<Id> = scan::reaches(f, tu)
            .iter()
            .map(|h| (h.def_file.clone(), h.name.clone()))
            .collect();
        for r in &reaches {
            if let Some(h) = s.headers.get_mut(r) {
                h.reached_by += 1;
            }
        }
        s.rows.push(FunctionRow {
            file: e.file.clone(),
            name: f.name.clone(),
            lines: f.lines,
            counts: counts_of(f, tu),
            builtins: scan::builtins_of(f),
            reaches,
        });
    }
    Ok(())
}

pub(crate) fn run(entries: &[&Entry], with_inlines: bool) -> Result<Survey> {
    let mut s = Survey::default();
    let mut pending = Vec::new();
    for e in entries {
        let loaded = frontend::load(e, with_inlines)?;
        s.stripped.insert(e.file.clone(), loaded.stripped);
        add_unit(&mut s, e, &loaded.tu, &mut pending)?;
    }
    let defined: BTreeSet<&str> = s
        .rows
        .iter()
        .map(|r| r.name.as_str())
        .chain(s.headers.keys().map(|(_, n)| n.as_str()))
        .collect();
    let mut externals: BTreeMap<String, External> = BTreeMap::new();
    for p in pending
        .into_iter()
        .filter(|p| !defined.contains(p.callee.as_str()))
    {
        let x = externals.entry(p.callee).or_default();
        x.sites += p.sites;
        if p.from_header {
            x.header_callers.insert(p.caller);
        } else {
            x.selected_callers.insert(p.caller);
        }
    }
    s.externals = externals;
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

fn status(counts: &Counts) -> String {
    if counts.is_empty() {
        return "ok".to_owned();
    }
    let parts: Vec<String> = counts
        .keys()
        .map(|(k, why)| format!("{k}: {why}"))
        .collect();
    format!("UNSUPPORTED {}", parts.join("; "))
}

const fn origin_name(o: Origin) -> &'static str {
    match o {
        Origin::MainFile => "main file",
        Origin::ProjectHeader => "project header",
        Origin::SystemHeader => "system header",
    }
}

pub(crate) fn render(s: &Survey) -> String {
    let mut o = String::new();
    selected(&mut o, s);
    headers(&mut o, s);
    let rows: Vec<&Counts> = s.rows.iter().map(|r| &r.counts).collect();
    construct_table(
        &mut o,
        "unsupported constructs in selected functions",
        &rows,
    );
    let rows: Vec<&Counts> = s.headers.values().map(|h| &h.counts).collect();
    construct_table(
        &mut o,
        "unsupported constructs in reachable header functions",
        &rows,
    );
    let mut builtins: BTreeMap<&str, usize> = BTreeMap::new();
    for b in s.rows.iter().flat_map(|r| &r.builtins) {
        *builtins.entry(b).or_default() += 1;
    }
    if !builtins.is_empty() {
        o.push_str(
            "\ncompiler builtins and atomic operations in selected functions \
             (represented as calls; functions using each)\n",
        );
        for (b, n) in builtins {
            let _ = writeln!(o, "{n:>9}  {b}");
        }
    }
    externals(&mut o, s);
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

fn selected(o: &mut String, s: &Survey) {
    let width = s.rows.iter().map(|r| r.name.len()).max().unwrap_or(8);
    for r in &s.rows {
        let _ = writeln!(
            o,
            "{}  {:width$}  {:>4} lines  {}",
            r.file,
            r.name,
            r.lines,
            status(&r.counts)
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
    let strict = s.rows.iter().filter(|r| s.strictly_ok(r)).count();
    let _ = writeln!(
        o,
        "total: {ok} of {n} functions fully represented ({}), in {} files",
        pct(ok, n),
        files.len()
    );
    let _ = writeln!(
        o,
        "total with reachable header functions: {strict} of {n} functions fully represented \
         together with every header function they reach ({})",
        pct(strict, n)
    );
}

fn headers(o: &mut String, s: &Survey) {
    if s.headers.is_empty() {
        return;
    }
    o.push_str(
        "\nreachable header functions (origin, lines, named from selected / from header \
         functions, selected functions reaching it, status)\n",
    );
    for ((file, name), h) in &s.headers {
        let _ = writeln!(
            o,
            "{file}  {name}  {}  {} lines  {}/{}  {}  {}",
            origin_name(h.origin),
            h.lines,
            h.sites_from_selected,
            h.sites_from_headers,
            h.reached_by,
            status(&h.counts)
        );
    }
    o.push('\n');
    for origin in [Origin::ProjectHeader, Origin::SystemHeader] {
        let of: Vec<&HeaderRow> = s.headers.values().filter(|h| h.origin == origin).collect();
        let ok = of.iter().filter(|h| h.counts.is_empty()).count();
        let sites: usize = of
            .iter()
            .map(|h| h.sites_from_selected + h.sites_from_headers)
            .sum();
        let _ = writeln!(
            o,
            "{}: {} reachable, {ok} fully represented, named at {sites} places",
            origin_name(origin),
            of.len()
        );
    }
}

fn construct_table(o: &mut String, title: &str, rows: &[&Counts]) {
    let mut table: BTreeMap<&(String, String), (usize, usize)> = BTreeMap::new();
    for counts in rows {
        for (k, n) in *counts {
            let e = table.entry(k).or_default();
            e.0 += 1;
            e.1 += n;
        }
    }
    if table.is_empty() {
        return;
    }
    let _ = writeln!(o, "\n{title}\nfunctions  occurrences  construct: reason");
    let mut rows: Vec<_> = table.into_iter().collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));
    for ((k, why), (fns, occ)) in rows {
        let _ = writeln!(o, "{fns:>9}  {occ:>11}  {k}: {why}");
    }
}

fn externals(o: &mut String, s: &Survey) {
    if s.externals.is_empty() {
        return;
    }
    let _ = writeln!(
        o,
        "\nexternal functions: {} named but defined nowhere in the selection\n\
         selected callers  header callers  places  function",
        s.externals.len()
    );
    let mut rows: Vec<(&String, &External)> = s.externals.iter().collect();
    rows.sort_by(|a, b| {
        b.1.selected_callers
            .len()
            .cmp(&a.1.selected_callers.len())
            .then_with(|| b.1.header_callers.len().cmp(&a.1.header_callers.len()))
            .then_with(|| a.0.cmp(b.0))
    });
    for (name, x) in rows {
        let _ = writeln!(
            o,
            "{:>16}  {:>14}  {:>6}  {name}",
            x.selected_callers.len(),
            x.header_callers.len(),
            x.sites
        );
    }
}
