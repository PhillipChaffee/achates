//! Writes the emitted Lake project and renders the summary.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use anyhow::{Context as _, Result};

use crate::emit::world::{StaticBlock, World};
use crate::emit::{Options, Row, graph, names};
use crate::ir::Origin;

fn ext_class(name: &str) -> String {
    format!("Ext.{}", names::ident(&name.replace('.', "_")))
}

fn emitted(r: &Row) -> bool {
    r.res.reasons.is_empty()
}

fn definition(r: &Row, recursive: bool) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "/-- C function `{}`, {}:{}.", r.name, r.file, r.line);
    for a in &r.res.assumptions {
        let _ = writeln!(s, "Assumes {a}.");
    }
    s.push_str("-/\n");
    let mut insts = String::new();
    for e in &r.res.exts {
        let _ = write!(insts, "[{}] ", ext_class(e));
    }
    let mut params = String::new();
    for p in &r.params {
        let _ = write!(params, " {p}");
    }
    let ret = r.sig.as_ref().map_or("Unit", |s| s.ret.as_str());
    let _ = write!(
        s,
        "def {} {insts}(fuel : Nat){params} : M {ret} :=",
        names::ident(&r.name)
    );
    if recursive {
        s.push_str("\n  match fuel with\n  | 0 => throw .outOfFuel\n  | fuel + 1 => do\n");
        for l in &r.res.lines {
            let _ = writeln!(s, "  {l}");
        }
        s.push_str("termination_by structural fuel\n");
    } else {
        s.push_str(" do\n");
        for l in &r.res.lines {
            let _ = writeln!(s, "{l}");
        }
    }
    s
}

fn module_text(root: &str, all: &[Row], rows: &[&Row]) -> String {
    let index: BTreeMap<&str, usize> = rows
        .iter()
        .enumerate()
        .map(|(i, r)| (r.key.as_str(), i))
        .collect();
    let edges: Vec<Vec<usize>> = rows
        .iter()
        .map(|r| {
            r.res
                .callees
                .iter()
                .filter_map(|c| index.get(c.as_str()).copied())
                .collect()
        })
        .collect();
    let mut imports: BTreeSet<String> = BTreeSet::new();
    let mut body = String::new();
    for comp in graph::components(&edges) {
        let members: Vec<&Row> = comp.iter().filter_map(|i| rows.get(*i).copied()).collect();
        let recursive = members.len() > 1 || members.iter().any(|r| r.res.callees.contains(&r.key));
        if members.len() > 1 {
            body.push_str("mutual\n\n");
        }
        for r in &members {
            body.push_str(&definition(r, recursive));
            body.push('\n');
        }
        if members.len() > 1 {
            body.push_str("end\n\n");
        }
    }
    let mine = rows.first().map_or("", |r| r.lean_file.as_str());
    for c in rows.iter().flat_map(|r| &r.res.callees) {
        if let Some(callee) = all
            .iter()
            .find(|r| r.key == *c)
            .filter(|r| r.lean_file != mine)
        {
            imports.insert(callee.lean_file.clone());
        }
    }
    let mut s = format!("import Achates\nimport {root}.Statics\nimport {root}.Externals\n");
    for m in imports {
        let _ = writeln!(s, "import {root}.{m}");
    }
    let module = rows.first().map_or("", |r| r.module.as_str());
    let _ = write!(
        s,
        "\n/-! Emitted by Achates from C; do not edit. -/\n\nset_option linter.unusedVariables false\nset_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\n\nopen Achates\n\nnamespace {root}.{module}\n\n{body}end {root}.{module}\n"
    );
    s
}

fn statics_text(root: &str, w: &World) -> String {
    let mut s = format!(
        "import Achates\n\n/-! Objects with static storage: string literals and file-scope variables.\nEmitted by Achates from C; do not edit. -/\n\nset_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\n\nopen Achates\n\nnamespace {root}.Statics\n\n"
    );
    let mut allocs = Vec::new();
    let mut readonly = Vec::new();
    for (id, b) in w.statics.blocks.iter().enumerate() {
        match b {
            StaticBlock::Str { bytes, size } => {
                let _ = writeln!(s, "def str_{id} : Ptr := .obj {id} 0");
                let list: Vec<String> = bytes.iter().map(u8::to_string).collect();
                allocs.push(format!(
                    "  Mem.allocString {id} [{}] {size}",
                    list.join(", ")
                ));
            }
            StaticBlock::Obj {
                lean,
                size,
                align,
                readonly: ro,
                what,
            } => {
                let _ = writeln!(
                    s,
                    "/-- C object `{what}`. -/\ndef {lean} : Ptr := .obj {id} 0"
                );
                allocs.push(format!("  Mem.allocStatic {id} {size} {align}"));
                if *ro {
                    readonly.push(format!("  Mem.setReadonly {id}"));
                }
            }
        }
    }
    let mut steps = Vec::new();
    for (i, chunk) in allocs.chunks(50).enumerate() {
        let _ = writeln!(s, "\ndef alloc_{i} : M Unit := do\n{}", chunk.join("\n"));
        steps.push(format!("  alloc_{i}"));
    }
    for (id, lines) in &w.statics.inits {
        let text: Vec<&str> = lines.iter().flat_map(|l| l.lines()).collect();
        for (i, chunk) in split(&text, 60).into_iter().enumerate() {
            let _ = writeln!(
                s,
                "\ndef init_{id}_{i} : M Unit := do\n{}",
                chunk.join("\n")
            );
            steps.push(format!("  init_{id}_{i}"));
        }
    }
    steps.extend(readonly);
    steps.push("  pure ()".to_owned());
    let _ = write!(
        s,
        "\n/-- Allocates and initialises every static object; run it before any emitted function. -/\ndef init : M Unit := do\n{}\n\nend {root}.Statics\n",
        steps.join("\n")
    );
    s
}

/// Names bound by `let` on a line, and names of that form it uses.
fn temps(line: &str) -> (Option<&str>, Vec<&str>) {
    let bound = line
        .trim_start()
        .strip_prefix("let ")
        .and_then(|r| r.split([' ', ':']).next());
    let used = line
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|w| {
            w.strip_prefix('t')
                .is_some_and(|r| !r.is_empty() && r.chars().all(|c| c.is_ascii_digit()))
        })
        .collect();
    (bound, used)
}

/// Cuts a long run of initialisation lines into definitions Lean can
/// elaborate, never between a `let` and a use of what it binds.
fn split<'a>(lines: &[&'a str], size: usize) -> Vec<Vec<&'a str>> {
    let mut last_use: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, l) in lines.iter().enumerate() {
        for u in temps(l).1 {
            last_use.insert(u, i);
        }
    }
    let mut out = Vec::new();
    let mut cur: Vec<&str> = Vec::new();
    let mut open_until = 0;
    for (i, l) in lines.iter().enumerate() {
        if cur.len() >= size && i > open_until && l.starts_with("  ") && !l.starts_with("   ") {
            out.push(std::mem::take(&mut cur));
        }
        if let Some(b) = temps(l).0 {
            open_until = open_until.max(last_use.get(b).copied().unwrap_or(i));
        }
        cur.push(l);
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn externals_text(root: &str, w: &World, used: &BTreeSet<String>) -> String {
    let mut s = format!(
        "import Achates\n\n/-! Functions the emitted code calls and the selection does not define.\nEach is a parameter: a definition that needs one says so in its signature.\nEmitted by Achates from C; do not edit. -/\n\nopen Achates\n\nnamespace {root}\n\n"
    );
    for name in used {
        if let Some(Ok(arrow)) = w.exts.get(name) {
            let _ = writeln!(
                s,
                "/-- C function `{name}`. -/\nclass {} where\n  call : {arrow}\n",
                ext_class(name)
            );
        }
    }
    let _ = writeln!(s, "end {root}");
    s
}

fn put(path: &Path, text: &str) -> Result<()> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).with_context(|| format!("creating {}", dir.display()))?;
    }
    std::fs::write(path, text).with_context(|| format!("writing {}", path.display()))
}

fn relative(from: &Path, to: &Path) -> String {
    let (Ok(from), Ok(to)) = (std::fs::canonicalize(from), std::fs::canonicalize(to)) else {
        return to.display().to_string();
    };
    let (a, b): (Vec<_>, Vec<_>) = (from.components().collect(), to.components().collect());
    let same = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let mut parts: Vec<String> = a.iter().skip(same).map(|_| "..".to_owned()).collect();
    parts.extend(
        b.iter()
            .skip(same)
            .map(|c| c.as_os_str().to_string_lossy().into_owned()),
    );
    if parts.is_empty() {
        ".".to_owned()
    } else {
        parts.join("/")
    }
}

#[derive(serde::Serialize)]
struct Status<'a> {
    file: &'a str,
    function: &'a str,
    line: u64,
    origin: Origin,
    lean: Option<String>,
    outcome: &'static str,
    reasons: &'a [String],
    assumptions: &'a BTreeSet<String>,
    externals: &'a BTreeSet<String>,
    models: &'a BTreeSet<String>,
}

pub(crate) fn write(opts: &Options, w: &World, rows: &[Row]) -> Result<()> {
    let root = &opts.name;
    let out = &opts.out;
    std::fs::create_dir_all(out).with_context(|| format!("creating {}", out.display()))?;
    let src = out.join(root);
    if src.exists() {
        std::fs::remove_dir_all(&src).with_context(|| format!("clearing {}", src.display()))?;
    }
    let mut by_module: BTreeMap<&str, Vec<&Row>> = BTreeMap::new();
    for r in rows.iter().filter(|r| emitted(r)) {
        by_module.entry(&r.lean_file).or_default().push(r);
    }
    let mut top = format!("import {root}.Statics\nimport {root}.Externals\n");
    for (module, rs) in &by_module {
        let path = src.join(format!("{}.lean", module.replace('.', "/")));
        put(&path, &module_text(root, rows, rs))?;
        let _ = writeln!(top, "import {root}.{module}");
    }
    let used: BTreeSet<String> = rows
        .iter()
        .filter(|r| emitted(r))
        .flat_map(|r| r.res.exts.iter().cloned())
        .collect();
    put(&src.join("Statics.lean"), &statics_text(root, w))?;
    put(&src.join("Externals.lean"), &externals_text(root, w, &used))?;
    put(&out.join(format!("{root}.lean")), &top)?;
    put(&out.join("lean-toolchain"), "leanprover/lean4:v4.36.0\n")?;
    put(
        &out.join("lakefile.toml"),
        &format!(
            "name = \"{}\"\ndefaultTargets = [\"{root}\"]\n\n[[require]]\nname = \"achates\"\npath = \"{}\"\n\n[[lean_lib]]\nname = \"{root}\"\nleanOptions = {{ autoImplicit = false, relaxedAutoImplicit = false }}\n",
            root.to_lowercase(),
            relative(out, &opts.runtime)
        ),
    )?;
    let status: Vec<Status<'_>> = rows
        .iter()
        .map(|r| Status {
            file: &r.file,
            function: &r.name,
            line: r.line,
            origin: r.origin,
            lean: emitted(r).then(|| format!("{root}.{}.{}", r.module, names::ident(&r.name))),
            outcome: if emitted(r) { "emitted" } else { "not emitted" },
            reasons: &r.res.reasons,
            assumptions: &r.res.assumptions,
            externals: &r.res.exts,
            models: &r.res.models,
        })
        .collect();
    put(
        &out.join("status.json"),
        &(serde_json::to_string_pretty(&status)? + "\n"),
    )
}

fn tally<'a>(items: impl Iterator<Item = &'a String>) -> Vec<(usize, &'a str)> {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for i in items {
        *counts.entry(i.as_str()).or_default() += 1;
    }
    let mut v: Vec<(usize, &str)> = counts.into_iter().map(|(k, n)| (n, k)).collect();
    v.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(b.1)));
    v
}

pub(crate) fn summary(w: &World, rows: &[Row]) -> String {
    let mut o = String::new();
    let mut files: BTreeMap<(bool, &str), (usize, usize)> = BTreeMap::new();
    for r in rows {
        let header = r.origin != Origin::MainFile;
        let e = files.entry((header, &r.file)).or_default();
        e.0 += 1;
        e.1 += usize::from(emitted(r));
        if emitted(r) {
            let _ = writeln!(o, "{}:{} {}: emitted", r.file, r.line, r.name);
        } else {
            let _ = writeln!(
                o,
                "{}:{} {}: not emitted: {}",
                r.file,
                r.line,
                r.name,
                r.res.reasons.join("; ")
            );
        }
    }
    for header in [false, true] {
        let _ = writeln!(
            o,
            "\n{} functions, emitted of total, per file:",
            if header { "Header" } else { "Selected" }
        );
        let (mut n, mut ok) = (0, 0);
        for ((_, f), (t, e)) in files.iter().filter(|((h, _), _)| *h == header) {
            let _ = writeln!(o, "  {e:>4} / {t:<4} {f}");
            n += t;
            ok += e;
        }
        let _ = writeln!(o, "  {ok:>4} / {n:<4} total");
    }
    let closed = rows
        .iter()
        .filter(|r| emitted(r) && r.res.exts.iter().all(|e| !w.fns.contains_key(e)))
        .count();
    let _ = writeln!(
        o,
        "\nEmitted without taking any selection function as a parameter: {closed}"
    );
    let _ = writeln!(
        o,
        "\nReasons a function was not emitted, by number of functions:"
    );
    for (n, r) in tally(rows.iter().flat_map(|r| r.res.reasons.iter())) {
        let _ = writeln!(o, "  {n:>4}  {r}");
    }
    let _ = writeln!(
        o,
        "\nAssumptions, by number of emitted functions that rest on them:"
    );
    for (n, r) in tally(
        rows.iter()
            .filter(|r| emitted(r))
            .flat_map(|r| r.res.assumptions.iter()),
    ) {
        let _ = writeln!(o, "  {n:>4}  {r}");
    }
    let _ = writeln!(
        o,
        "\nModelled functions, by number of emitted functions that depend on them:"
    );
    for (n, r) in tally(
        rows.iter()
            .filter(|r| emitted(r))
            .flat_map(|r| r.res.models.iter()),
    ) {
        let _ = writeln!(o, "  {n:>4}  {r}");
    }
    let _ = writeln!(
        o,
        "\nFunctions taken as parameters, by number of emitted functions that depend on them:"
    );
    for (n, r) in tally(
        rows.iter()
            .filter(|r| emitted(r))
            .flat_map(|r| r.res.exts.iter()),
    ) {
        let note = if w.fns.contains_key(r) {
            " (in the selection: not emitted, or in a call cycle across files)"
        } else {
            ""
        };
        let _ = writeln!(o, "  {n:>4}  {r}{note}");
    }
    o
}
