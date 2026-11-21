//! From a compilation database entry to a [`TranslationUnit`].

use std::collections::{BTreeMap, BTreeSet};

use anyhow::Result;
use serde_json::Value;

use crate::clang;
use crate::compdb::{self, Entry, normalize};
use crate::convert::{Unit, kind, tags_in};
use crate::ir::{Function, TranslationUnit};
use crate::probe;
use crate::scan;
use crate::target;
use crate::types::{TagName, TypeCtx};

#[derive(Debug)]
pub(crate) struct Loaded {
    pub(crate) tu: TranslationUnit,
    /// Arguments removed from the database's command line.
    pub(crate) stripped: Vec<String>,
}

pub(crate) fn load(entry: &Entry) -> Result<Loaded> {
    let args = compdb::clang_args(entry)?;
    let target = target::query(entry, &args)?;
    let raw = clang::load_ast(entry, &args)?;
    let is_main = |f: &str| normalize(&entry.directory.join(f)) == entry.path;
    let mut unit = Unit::new(TypeCtx::new(target.clone()), &raw);
    let mut roots: Vec<&Value> = raw.functions.iter().collect();
    roots.extend(
        raw.decls.iter().filter(|d| {
            kind(d) == "VarDecl" && clang::node_loc(d).is_some_and(|l| is_main(&l.file))
        }),
    );
    let enum_types = probe::run(entry, &args, &mut unit, &roots)?;
    let functions: Vec<Function> = raw.functions.iter().map(|f| unit.function(f)).collect();

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
    let mut records = BTreeMap::new();
    let mut todo: Vec<_> = record_keys.into_iter().collect();
    while let Some(key) = todo.pop() {
        if records.contains_key(&key) {
            continue;
        }
        let def = unit.record_def(&key);
        let mut more = BTreeSet::new();
        for fld in def.fields.iter().flatten() {
            tags_in(&fld.ty, &mut more, &mut enum_names);
        }
        todo.extend(more.into_iter().filter(|k| !records.contains_key(k)));
        records.insert(key, def);
    }
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
