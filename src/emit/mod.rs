//! `achates emit`: Lean definitions for the selected C functions, as a
//! Lake project, with the status of every function.

mod expr;
mod func;
mod graph;
mod layout;
mod names;
mod order;
mod project;
mod world;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use anyhow::{Result, bail};

use crate::compdb::{self, Entry};
use crate::dump;
use crate::frontend;
use crate::ir::{Function, Linkage, Origin, Storage, TranslationUnit};
use func::{Emitted, FnEmitter};
use layout::Layouts;
use names::Sig;
use world::{FnMeta, Unit, World};

#[derive(Debug)]
pub(crate) struct Options {
    pub(crate) out: PathBuf,
    /// Root namespace and library name of the emitted project.
    pub(crate) name: String,
    /// Directory of the Lean runtime the project depends on.
    pub(crate) runtime: PathBuf,
}

struct Loaded {
    tu: TranslationUnit,
    lay: Layouts,
    float_flags: Vec<String>,
}

/// Flags that let the compiler compute floating-point results other than
/// the IEEE ones the Lean definitions compute.
const FLOAT_FLAGS: &[&str] = &[
    "-ffast-math",
    "-Ofast",
    "-fno-signed-zeros",
    "-ffinite-math-only",
    "-funsafe-math-optimizations",
    "-fassociative-math",
    "-freciprocal-math",
    "-frounding-math",
    "-ffp-contract=fast",
    "-mfma",
];

fn load(e: &Entry) -> Result<Loaded> {
    let l = frontend::load(e, true)?;
    let t = &l.tu.target;
    if t.char_bits != 8 || t.pointer_bits != 64 || t.int_bits != 32 || t.long_bits != 64 {
        bail!("{}: the Lean runtime models x86-64 Linux only (8-bit bytes, 32-bit int, 64-bit long and pointers)", e.file);
    }
    let args = compdb::clang_args(e)?;
    let mut lay = layout::probe(e, &args, &l.tu)?;
    for (name, def) in &l.tu.enums {
        if let Ok(i) = &def.underlying {
            lay.enums.insert(name.clone(), *i);
        }
    }
    let float_flags = e
        .argv
        .iter()
        .filter(|a| FLOAT_FLAGS.contains(&a.as_str()) || a.starts_with("-march=") || a.starts_with("-mfpmath="))
        .cloned()
        .collect();
    Ok(Loaded {
        tu: l.tu,
        lay,
        float_flags,
    })
}

fn common_dir(paths: &[PathBuf]) -> PathBuf {
    let mut it = paths.iter();
    let Some(first) = it.next().and_then(|p| p.parent()) else {
        return PathBuf::new();
    };
    let mut root: Vec<Component<'_>> = first.components().collect();
    for p in it {
        let comps: Vec<Component<'_>> = p.parent().map(|d| d.components().collect()).unwrap_or_default();
        let same = root.iter().zip(&comps).take_while(|(a, b)| a == b).count();
        root.truncate(same);
    }
    root.iter().collect()
}

/// Lean module of a C file: its path below the directory all project files
/// share, or `Sys.<file>` for a system header.
fn module_of(file: &str, root: &Path, system: bool) -> String {
    let p = Path::new(file);
    let parts: Vec<String> = match p.strip_prefix(root) {
        Ok(rel) if !system => rel.components().map(|c| names::module_part(&c.as_os_str().to_string_lossy())).collect(),
        _ => vec![
            "Sys".to_owned(),
            names::module_part(&p.file_name().map(|f| f.to_string_lossy().into_owned()).unwrap_or_default()),
        ],
    };
    parts.join(".")
}

/// A function of the selection and where its IR is.
struct Owned {
    key: String,
    module: String,
    tu: usize,
    index: usize,
    /// Set when two units give the header function different bodies.
    conflict: Option<String>,
}

struct Selection {
    units: Vec<Loaded>,
    owned: Vec<Owned>,
    /// Per unit: function name to key.
    local_fns: Vec<BTreeMap<String, String>>,
    /// Per unit: global name to key.
    globals: Vec<BTreeMap<String, String>>,
    /// Per unit: module of its main file.
    main_module: Vec<String>,
}

fn fn_key(f: &Function, module: &str) -> String {
    if f.linkage == Linkage::External {
        f.name.clone()
    } else {
        format!("{module}.{}", f.name)
    }
}

fn select(units: Vec<Loaded>, entries: &[&Entry]) -> Selection {
    let mut files: Vec<PathBuf> = entries.iter().map(|e| e.path.clone()).collect();
    for u in &units {
        files.extend(u.tu.functions.iter().filter(|f| f.origin == Origin::ProjectHeader).map(|f| PathBuf::from(&f.def_file)));
    }
    let root = common_dir(&files);
    let mut owned: Vec<Owned> = Vec::new();
    let mut seen: BTreeMap<String, (usize, String)> = BTreeMap::new();
    let mut local_fns = Vec::new();
    let mut main_module = Vec::new();
    for (ti, (u, e)) in units.iter().zip(entries).enumerate() {
        main_module.push(module_of(&e.path.to_string_lossy(), &root, false));
        let mut names = BTreeMap::new();
        for (fi, f) in u.tu.functions.iter().enumerate() {
            let module = module_of(&f.def_file, &root, f.origin == Origin::SystemHeader);
            let key = fn_key(f, &module);
            names.insert(f.name.clone(), key.clone());
            let print = dump::fingerprint(f);
            match seen.get(&key) {
                None => {
                    seen.insert(key.clone(), (owned.len(), print));
                    owned.push(Owned { key, module, tu: ti, index: fi, conflict: None });
                }
                Some((at, old)) if *old != print => {
                    if let Some(o) = owned.get_mut(*at) {
                        o.conflict = Some(format!("defined differently in {} and {}", units.get(o.tu).map_or("", |u| u.tu.file.as_str()), u.tu.file));
                    }
                }
                Some(_) => {}
            }
        }
        local_fns.push(names);
    }
    let defined: BTreeSet<&str> = units
        .iter()
        .flat_map(|u| u.tu.globals.values())
        .filter(|g| g.storage == Storage::None)
        .map(|g| g.name.as_str())
        .collect();
    let globals = units
        .iter()
        .zip(&main_module)
        .map(|(u, m)| {
            u.tu.globals
                .values()
                .filter_map(|g| match g.storage {
                    Storage::Static => Some((g.name.clone(), format!("{m}.{}", g.name))),
                    _ if defined.contains(g.name.as_str()) => Some((g.name.clone(), g.name.clone())),
                    _ => None,
                })
                .collect()
        })
        .collect();
    Selection { units, owned, local_fns, globals, main_module }
}

impl Selection {
    fn function(&self, o: &Owned) -> Option<&Function> {
        self.units.get(o.tu)?.tu.functions.get(o.index)
    }

    fn unit(&self, ti: usize) -> Option<Unit<'_>> {
        let l = self.units.get(ti)?;
        Some(Unit {
            tu: &l.tu,
            lay: &l.lay,
            local_fns: self.local_fns.get(ti)?.clone(),
            globals: self.globals.get(ti)?.clone(),
            float_flags: l.float_flags.clone(),
        })
    }
}

/// Fills the world with what does not change between rounds.
fn prepare(sel: &Selection) -> World {
    let mut w = World::default();
    for o in &sel.owned {
        let Some(f) = sel.function(o) else { continue };
        if f.linkage == Linkage::External {
            w.external_defs.insert(f.name.clone(), o.key.clone());
        }
        w.fns.insert(o.key.clone(), FnMeta { key: o.key.clone(), module: o.module.clone(), name: f.name.clone(), sig: Err("not computed".into()) });
    }
    let resolve = |ti: usize, name: &str| -> Option<String> {
        sel.local_fns.get(ti)?.get(name).or_else(|| w.external_defs.get(name)).cloned()
    };
    // Import order: a module comes after the modules its functions call.
    let modules: Vec<String> = sel.owned.iter().map(|o| o.module.clone()).collect::<BTreeSet<_>>().into_iter().collect();
    let pos_of = |m: &str| modules.iter().position(|x| x == m);
    let mut edges = vec![Vec::new(); modules.len()];
    for o in &sel.owned {
        let Some(f) = sel.function(o) else { continue };
        let refs: Vec<Option<String>> = crate::scan::refs_of(f).keys().map(|n| resolve(o.tu, n)).collect();
        for k in refs.iter().flatten() {
            if let (Some(a), Some(b)) = (pos_of(&o.module), w.fns.get(k).and_then(|m| pos_of(&m.module)))
                && a != b
                && let Some(e) = edges.get_mut(a)
            {
                e.push(b);
            }
        }
    }
    let mut pos = BTreeMap::new();
    for m in graph::components(&edges).into_iter().flatten() {
        if let Some(name) = modules.get(m) {
            pos.insert(name.clone(), pos.len());
        }
    }
    w.module_pos = pos;
    w.writes = writes(sel, &w);
    w
}

/// Least fixed point of "may write memory its caller can see".
fn writes(sel: &Selection, w: &World) -> BTreeMap<String, bool> {
    let mut out: BTreeMap<String, bool> = sel.owned.iter().map(|o| (o.key.clone(), false)).collect();
    loop {
        let mut changed = false;
        for o in &sel.owned {
            let Some(f) = sel.function(o) else { continue };
            let names = sel.local_fns.get(o.tu);
            let cw = |name: Option<&str>| {
                name.is_none_or(|n| match names.and_then(|m| m.get(n)).or_else(|| w.external_defs.get(n)) {
                    Some(k) => out.get(k).copied().unwrap_or(true),
                    None => world::MODELS.iter().find(|m| m.name == n).is_none_or(|m| m.writes),
                })
            };
            if !out.get(&o.key).copied().unwrap_or(true) && order::writes_memory(f, &cw) {
                out.insert(o.key.clone(), true);
                changed = true;
            }
        }
        if !changed {
            return out;
        }
    }
}

/// One selected function after emission.
pub(crate) struct Row {
    pub(crate) key: String,
    pub(crate) module: String,
    pub(crate) name: String,
    pub(crate) file: String,
    pub(crate) line: u64,
    pub(crate) origin: Origin,
    pub(crate) params: Vec<String>,
    pub(crate) sig: Option<Sig>,
    pub(crate) res: Emitted,
}

fn static_objects(sel: &Selection, w: &mut World) {
    for ti in 0..sel.units.len() {
        let (Some(unit), Some(module)) = (sel.unit(ti), sel.main_module.get(ti)) else { continue };
        let mut em = FnEmitter::new(&unit, w, module, "");
        for g in unit.tu.globals.values().filter(|g| g.storage != Storage::Extern) {
            let Some(key) = unit.globals.get(&g.name) else { continue };
            if em.w.statics.globals.contains_key(key) {
                continue;
            }
            let lean = format!("g_{}", key.replace('.', "_"));
            if let Err(e) = em.static_object(key, &lean, &g.ty, g.init.as_ref()) {
                em.w.statics.globals.insert(key.clone(), Err(e));
            }
            em.res.reasons.clear();
        }
    }
}

fn round(sel: &Selection, w: &mut World) -> Vec<Row> {
    w.statics = world::Statics::default();
    w.exts.clear();
    static_objects(sel, w);
    let mut rows = Vec::new();
    for o in &sel.owned {
        let (Some(f), Some(unit)) = (sel.function(o), sel.unit(o.tu)) else { continue };
        let em = FnEmitter::new(&unit, w, &o.module, &f.name);
        let (mut res, params, sig) = em.function(f);
        if let Some(c) = &o.conflict {
            res.reasons.push(c.clone());
        }
        rows.push(Row {
            key: o.key.clone(),
            module: o.module.clone(),
            name: f.name.clone(),
            file: f.loc.as_ref().map_or_else(|| f.def_file.clone(), |l| l.file.clone()),
            line: f.loc.as_ref().map_or(0, |l| l.line),
            origin: f.origin,
            params,
            sig,
            res,
        });
    }
    rows
}

/// What each emitted function needs through the functions it calls.
fn close(rows: &mut [Row]) {
    loop {
        let mut changed = false;
        let snapshot: BTreeMap<String, (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>)> = rows
            .iter()
            .map(|r| (r.key.clone(), (r.res.exts.clone(), r.res.models.clone(), r.res.assumptions.clone())))
            .collect();
        for r in rows.iter_mut() {
            let before = r.res.exts.len() + r.res.models.len() + r.res.assumptions.len();
            for c in &r.res.callees {
                if let Some((e, m, a)) = snapshot.get(c) {
                    r.res.exts.extend(e.iter().cloned());
                    r.res.models.extend(m.iter().cloned());
                    r.res.assumptions.extend(a.iter().cloned());
                }
            }
            changed |= before != r.res.exts.len() + r.res.models.len() + r.res.assumptions.len();
        }
        if !changed {
            return;
        }
    }
}

pub(crate) fn run(entries: &[&Entry], opts: &Options) -> Result<String> {
    let units = entries.iter().map(|e| load(e)).collect::<Result<Vec<_>>>()?;
    let sel = select(units, entries);
    let mut w = prepare(&sel);
    for o in &sel.owned {
        if let (Some(f), Some(unit)) = (sel.function(o), sel.unit(o.tu)) {
            let sig = FnEmitter::new(&unit, &mut w, &o.module, &f.name).signature(f);
            if let Some(m) = w.fns.get_mut(&o.key) {
                m.sig = sig.ok_or_else(|| "type without a Lean counterpart".to_owned());
            }
        }
    }
    w.addressed.clear();
    let mut rows = Vec::new();
    for _ in 0..8 {
        let before = (w.refused.clone(), w.addressed.clone());
        rows = round(&sel, &mut w);
        w.refused = rows.iter().filter(|r| !r.res.reasons.is_empty()).map(|r| r.key.clone()).collect();
        if before == (w.refused.clone(), w.addressed.clone()) {
            break;
        }
    }
    close(&mut rows);
    project::write(opts, &w, &rows)?;
    Ok(project::summary(&w, &rows))
}
