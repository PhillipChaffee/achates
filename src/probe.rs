//! Constants clang computes but does not print in its JSON: the value of
//! `sizeof` and `_Alignof`, and the integer type each enum is compatible
//! with. Achates asks clang for them by compiling a second file that
//! includes the first and declares one array per question, whose length is
//! the answer.

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use anyhow::{Context as _, Result, bail};
use serde_json::Value;

use crate::clang::parse_many;
use crate::compdb::{ClangArgs, Entry};
use crate::convert::{Unit, inner, kind, probe_key, text, type_of};
use crate::ir::TypeTrait;
use crate::tools;
use crate::types::{IntKind, IntType, TagName, Type};

const PREFIX: &str = "__achates_probe_";

/// The `_Generic` associations; an enum selects its compatible type.
const GENERIC_INTS: &[(IntKind, &str)] = &[
    (IntKind::Char, "char"),
    (IntKind::SChar, "signed char"),
    (IntKind::UChar, "unsigned char"),
    (IntKind::Short, "short"),
    (IntKind::UShort, "unsigned short"),
    (IntKind::Int, "int"),
    (IntKind::UInt, "unsigned int"),
    (IntKind::Long, "long"),
    (IntKind::ULong, "unsigned long"),
    (IntKind::LongLong, "long long"),
    (IntKind::ULongLong, "unsigned long long"),
];

fn enum_expr(name: &TagName) -> Option<String> {
    let t = match name {
        TagName::Tag(n) => format!("enum {n}"),
        TagName::Typedef(n) => n.clone(),
        TagName::Anon(_) => return None,
    };
    let assoc: Vec<String> = GENERIC_INTS
        .iter()
        .zip(1..)
        .map(|((_, c), i)| format!("{c}: {i}"))
        .collect();
    Some(format!(
        "_Generic(({t})0, {}, default: 0)",
        assoc.join(", ")
    ))
}

/// Collects the type traits under `v`, as the converter will key them.
fn collect(unit: &mut Unit<'_>, v: &Value, out: &mut BTreeSet<String>) {
    if kind(v) == "UnaryExprOrTypeTraitExpr" {
        let t = match text(v, "name") {
            Some("sizeof") => Some(TypeTrait::Size),
            Some("alignof") => Some(TypeTrait::Align),
            Some("__alignof") => Some(TypeTrait::PreferredAlign),
            _ => None,
        };
        let ty_obj = v.get("argType").or_else(|| {
            let mut e = inner(v).first()?;
            while matches!(kind(e), "ParenExpr" | "ConstantExpr") {
                e = inner(e).first()?;
            }
            e.get("type")
        });
        if let Some(t) = t {
            let q = type_of(&mut unit.types, ty_obj);
            if let Some(k) = probe_key(t, &q) {
                out.insert(k);
            }
        }
    }
    for c in inner(v) {
        collect(unit, c, out);
    }
    if let Some(a) = v.get("array_filler").and_then(Value::as_array) {
        for c in a {
            collect(unit, c, out);
        }
    }
}

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Asks clang every question under `roots`, stores the answers in
/// `unit.probes`, and returns each enum's compatible integer type.
pub(crate) fn run(
    entry: &Entry,
    args: &ClangArgs,
    unit: &mut Unit<'_>,
    roots: &[&Value],
) -> Result<HashMap<TagName, Result<IntType, String>>> {
    let mut traits = BTreeSet::new();
    for r in roots {
        collect(unit, r, &mut traits);
    }
    let enums = unit.probe_enums();
    let mut questions: Vec<String> = traits.into_iter().collect();
    let enum_start = questions.len();
    let enum_names: Vec<TagName> = enums
        .into_iter()
        .filter(|e| enum_expr(e).is_some())
        .collect();
    questions.extend(enum_names.iter().filter_map(enum_expr));
    let answers = ask(entry, args, &questions)?;
    for (q, a) in questions.iter().zip(&answers).take(enum_start) {
        unit.probes.insert(q.clone(), a.clone());
    }
    let mut out = HashMap::new();
    for (name, a) in enum_names
        .into_iter()
        .zip(answers.into_iter().skip(enum_start))
    {
        let r = a.and_then(|i| {
            let idx = usize::try_from(i).map_err(|e| e.to_string())?;
            let (k, _) = idx
                .checked_sub(1)
                .and_then(|j| GENERIC_INTS.get(j))
                .ok_or("not compatible with any standard integer type")?;
            match unit.types.parse(k.c_name()).ty {
                Type::Int(it) => Ok(it),
                other => Err(format!("unexpected type {other}")),
            }
        });
        out.insert(name, r);
    }
    Ok(out)
}

/// Evaluates each integer constant expression with clang. An expression
/// clang rejects gets its error message, and the rest are asked again.
pub(crate) fn ask(
    entry: &Entry,
    args: &ClangArgs,
    questions: &[String],
) -> Result<Vec<Result<u64, String>>> {
    let mut answers: Vec<Option<Result<u64, String>>> = vec![None; questions.len()];
    if questions.is_empty() {
        return Ok(vec![]);
    }
    let dir = std::env::temp_dir().join(format!(
        "achates-{}-{}",
        std::process::id(),
        COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;
    let result = ask_in(entry, args, questions, &mut answers, &dir.join("probe.c"));
    let _ = std::fs::remove_dir_all(&dir);
    result?;
    Ok(answers
        .into_iter()
        .map(|a| a.unwrap_or_else(|| Err("clang printed no answer".into())))
        .collect())
}

fn ask_in(
    entry: &Entry,
    args: &ClangArgs,
    questions: &[String],
    answers: &mut [Option<Result<u64, String>>],
    path: &PathBuf,
) -> Result<()> {
    for _attempt in 0..4 {
        let mut src = format!("#include \"{}\"\n", entry.path.display());
        let mut line_of = HashMap::new();
        for (i, q) in questions.iter().enumerate() {
            if answers.get(i).is_some_and(Option::is_none) {
                line_of.insert(src.lines().count() + 1, i);
                let _ = writeln!(src, "typedef char {PREFIX}{i}[({q}) + 1];");
            }
        }
        if line_of.is_empty() {
            return Ok(());
        }
        std::fs::write(path, &src).with_context(|| format!("writing {}", path.display()))?;
        let mut cmd = args.flags.clone();
        cmd.extend(["-fsyntax-only", "-Xclang", "-ast-dump=json", "-Xclang"].map(String::from));
        cmd.push(format!("-ast-dump-filter={PREFIX}"));
        cmd.push(path.display().to_string());
        let clang = tools::clang()?;
        let out = std::process::Command::new(clang)
            .args(&cmd)
            .current_dir(&entry.directory)
            .output()
            .with_context(|| {
                format!("starting {} for probes of {}", clang.display(), entry.file)
            })?;
        if out.status.success() {
            for v in parse_many(&out.stdout)? {
                read_answer(&v, answers);
            }
            return Ok(());
        }
        let err = String::from_utf8_lossy(&out.stderr);
        let marker = format!("{}:", path.display());
        let mut blamed = false;
        for l in err.lines() {
            let Some(rest) = l.strip_prefix(&marker) else {
                continue;
            };
            let mut parts = rest.splitn(3, ':');
            let line = parts.next().and_then(|n| n.parse::<usize>().ok());
            let msg = parts.nth(1).unwrap_or("").trim();
            if let Some(i) = line.and_then(|n| line_of.get(&n))
                && msg.starts_with("error")
                && let Some(slot) = answers.get_mut(*i)
            {
                *slot = Some(Err(msg.trim_start_matches("error:").trim().to_owned()));
                blamed = true;
            }
        }
        if !blamed {
            bail!(
                "{} failed on the probes for {}:\n{err}",
                clang.display(),
                entry.file
            );
        }
    }
    bail!("probes for {} kept failing", entry.file)
}

fn read_answer(v: &Value, answers: &mut [Option<Result<u64, String>>]) {
    let Some(i) = text(v, "name")
        .and_then(|n| n.strip_prefix(PREFIX))
        .and_then(|n| n.parse::<usize>().ok())
    else {
        return;
    };
    let len = v
        .get("type")
        .and_then(|t| text(t, "qualType"))
        .and_then(|q| q.strip_prefix("char["))
        .and_then(|q| q.strip_suffix(']'))
        .and_then(|q| q.parse::<u64>().ok());
    if let Some(slot) = answers.get_mut(i) {
        *slot = Some(
            len.and_then(|n| n.checked_sub(1))
                .ok_or_else(|| "clang's answer could not be read".into()),
        );
    }
}
