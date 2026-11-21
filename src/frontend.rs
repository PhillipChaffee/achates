//! From a compilation database entry to a [`TranslationUnit`].

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use anyhow::Result;
use serde_json::Value;

use crate::clang;
use crate::compdb::{self, Entry, normalize};
use crate::convert::{Unit, kind, raw_function_refs, tags_in, text};
use crate::ir::{Function, Origin, RecordDef, TranslationUnit};
use crate::probe;
use crate::scan;
use crate::target;
use crate::types::{RecordKind, TagName, TypeCtx};

#[derive(Debug)]
pub(crate) struct Loaded {
    pub(crate) tu: TranslationUnit,
    /// Arguments removed from the database's command line.
    pub(crate) stripped: Vec<String>,
}

/// Header functions with a body that the main file's functions reach
/// through references, transitively: calls and taken addresses both count,
/// since either way a back end needs the body.
fn reachable_headers(raw: &clang::RawTu) -> Vec<&Value> {
    let by_name: HashMap<&str, &Value> = raw
        .header_functions
        .iter()
        .filter_map(|f| Some((text(f, "name")?, f)))
        .collect();
    let mut todo = BTreeSet::new();
    for f in &raw.functions {
        raw_function_refs(f, &mut todo);
    }
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    while let Some(n) = todo.pop_first() {
        if !seen.insert(n.clone()) {
            continue;
        }
        if let Some(f) = by_name.get(n.as_str()) {
            out.push(*f);
            let mut more = BTreeSet::new();
            raw_function_refs(f, &mut more);
            todo.extend(more.into_iter().filter(|m| !seen.contains(m)));
        }
    }
    out
}

/// The definitions of `keys` and of every record their fields reach.
fn record_closure(
    unit: &mut Unit<'_>,
    keys: BTreeSet<(RecordKind, TagName)>,
    enum_names: &mut BTreeSet<TagName>,
) -> BTreeMap<(RecordKind, TagName), RecordDef> {
    let mut records = BTreeMap::new();
    let mut todo: Vec<_> = keys.into_iter().collect();
    while let Some(key) = todo.pop() {
        if records.contains_key(&key) {
            continue;
        }
        let def = unit.record_def(&key);
        let mut more = BTreeSet::new();
        for fld in def.fields.iter().flatten() {
            tags_in(&fld.ty, &mut more, enum_names);
        }
        todo.extend(more.into_iter().filter(|k| !records.contains_key(k)));
        records.insert(key, def);
    }
    records
}

pub(crate) fn load(entry: &Entry, with_inlines: bool) -> Result<Loaded> {
    let args = compdb::clang_args(entry)?;
    let target = target::query(entry, &args)?;
    let raw = clang::load_ast(entry, &args)?;
    let is_main = |f: &str| normalize(&entry.directory.join(f)) == entry.path;
    let headers = if with_inlines {
        reachable_headers(&raw)
    } else {
        vec![]
    };
    let system = if headers.is_empty() {
        HashSet::new()
    } else {
        clang::system_files(entry, &args)?
    };
    let mut unit = Unit::new(TypeCtx::new(target.clone()), &raw);
    let mut roots: Vec<&Value> = raw
        .functions
        .iter()
        .chain(headers.iter().copied())
        .collect();
    roots.extend(
        raw.decls.iter().filter(|d| {
            kind(d) == "VarDecl" && clang::node_loc(d).is_some_and(|l| is_main(&l.file))
        }),
    );
    let enum_types = probe::run(entry, &args, &mut unit, &roots)?;
    let def_file = |v: &Value| {
        clang::node_loc(v).map_or_else(String::new, |l| {
            normalize(&entry.directory.join(&l.file))
                .display()
                .to_string()
        })
    };
    let mut functions: Vec<Function> = raw
        .functions
        .iter()
        .map(|f| unit.function(f, Origin::MainFile, def_file(f)))
        .collect();
    for h in &headers {
        let file = def_file(h);
        let origin = if system.contains(std::path::Path::new(&file)) {
            Origin::SystemHeader
        } else {
            Origin::ProjectHeader
        };
        functions.push(unit.function(h, origin, file));
    }

    let mut record_keys = BTreeSet::new();
    let mut enum_names = BTreeSet::new();
    let mut global_names = BTreeSet::new();
    for f in &functions {
        for t in scan::types_of(f) {
            tags_in(t, &mut record_keys, &mut enum_names);
        }
        global_names.extend(f.globals.iter().cloned());
    }
    let mut globals = BTreeMap::new();
    for g in &global_names {
        if let Some(g) = unit.global(g, &is_main) {
            tags_in(&g.ty, &mut record_keys, &mut enum_names);
            globals.insert(g.name.clone(), g);
        }
    }
    let records = record_closure(&mut unit, record_keys, &mut enum_names);
    let enums = enum_names
        .into_iter()
        .map(|n| {
            let u = enum_types.get(&n).cloned().unwrap_or_else(|| {
                Err(match &n {
                    TagName::Anon(_) => {
                        "anonymous enum: clang cannot be asked about a type without a name".into()
                    }
                    _ => "enum never defined in this unit".into(),
                })
            });
            let def = unit.enum_def(&n, u);
            (n, def)
        })
        .collect();
    Ok(Loaded {
        tu: TranslationUnit {
            file: entry.file.clone(),
            target,
            functions,
            records,
            enums,
            globals,
        },
        stripped: args.stripped,
    })
}
