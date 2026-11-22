//! `achates emit`: Lean definitions for the selected C functions, as a
//! Lake project, with the status of every function.

pub(crate) mod expr;
mod func;
mod graph;
pub(crate) mod layout;
pub(crate) mod names;
pub(crate) mod order;
pub(crate) mod project;
pub(crate) mod world;

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
use order::Summary;
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
        bail!(
            "{}: the Lean runtime models x86-64 Linux only (8-bit bytes, 32-bit int, 64-bit long and pointers)",
            e.file
        );
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
        .filter(|a| {
            FLOAT_FLAGS.contains(&a.as_str())
                || a.starts_with("-march=")
                || a.starts_with("-mfpmath=")
        })
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
        let comps: Vec<Component<'_>> = p
            .parent()
            .map(|d| d.components().collect())
            .unwrap_or_default();
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
        Ok(rel) if !system => rel
            .components()
            .map(|c| names::module_part(&c.as_os_str().to_string_lossy()))
            .collect(),
        _ => vec![
            "Sys".to_owned(),
            names::module_part(
                &p.file_name()
                    .map(|f| f.to_string_lossy().into_owned())
                    .unwrap_or_default(),
            ),
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
        files.extend(
            u.tu.functions
                .iter()
                .filter(|f| f.origin == Origin::ProjectHeader)
                .map(|f| PathBuf::from(&f.def_file)),
        );
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
                    owned.push(Owned {
                        key,
                        module,
                        tu: ti,
                        index: fi,
                        conflict: None,
                    });
                }
                Some((at, old)) if *old != print => {
                    if let Some(o) = owned.get_mut(*at) {
                        o.conflict = Some(format!(
                            "defined differently in {} and {}",
                            units.get(o.tu).map_or("", |u| u.tu.file.as_str()),
                            u.tu.file
                        ));
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
                    _ if defined.contains(g.name.as_str()) => {
                        Some((g.name.clone(), g.name.clone()))
                    }
                    _ => None,
                })
                .collect()
        })
        .collect();
    Selection {
        units,
        owned,
        local_fns,
        globals,
        main_module,
    }
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
        w.fns.insert(
            o.key.clone(),
            FnMeta {
                key: o.key.clone(),
                module: o.module.clone(),
                name: f.name.clone(),
                sig: Err("not computed".into()),
            },
        );
    }
    let externals = w.external_defs.clone();
    let resolve = |ti: usize, name: &str| -> Option<String> {
        sel.local_fns
            .get(ti)?
            .get(name)
            .or_else(|| externals.get(name))
            .cloned()
    };
    place(sel, &mut w, &resolve);
    w.addr_taken = addresses(sel, &w);
    w.summaries = summaries(sel, &w);
    w
}

/// Chooses the Lean file of every function. A C file is one Lean file
/// unless its functions and another file's call each other; Lean imports
/// cannot be circular, so such a file continues in numbered parts, each
/// after the files its functions call.
fn place(sel: &Selection, w: &mut World, resolve: &dyn Fn(usize, &str) -> Option<String>) {
    let index: BTreeMap<&str, usize> = sel
        .owned
        .iter()
        .enumerate()
        .map(|(i, o)| (o.key.as_str(), i))
        .collect();
    let edges: Vec<Vec<usize>> = sel
        .owned
        .iter()
        .map(|o| {
            sel.function(o).map_or_else(Vec::new, |f| {
                order::direct_calls(f)
                    .iter()
                    .filter_map(|n| resolve(o.tu, n))
                    .filter_map(|k| index.get(k.as_str()).copied())
                    .collect()
            })
        })
        .collect();
    let modules: Vec<&str> = sel
        .owned
        .iter()
        .map(|o| o.module.as_str())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let module_of = |i: usize| {
        sel.owned
            .get(i)
            .and_then(|o| modules.iter().position(|m| *m == o.module))
    };
    let mut module_edges = vec![Vec::new(); modules.len()];
    for (i, callees) in edges.iter().enumerate() {
        for c in callees {
            if let (Some(a), Some(b)) = (module_of(i), module_of(*c))
                && a != b
                && let Some(e) = module_edges.get_mut(a)
            {
                e.push(b);
            }
        }
    }
    // Within a group of files that call each other, a function's layer is
    // the longest chain of calls below it that changes file; a file's
    // part holds one layer, so every call goes to an earlier part.
    let mut layer: BTreeMap<usize, usize> = BTreeMap::new();
    for comp in graph::components(&edges) {
        let same_module = comp
            .iter()
            .all(|i| module_of(*i) == comp.first().and_then(|f| module_of(*f)));
        let groups: Vec<Vec<usize>> = if same_module {
            vec![comp]
        } else {
            comp.into_iter().map(|i| vec![i]).collect()
        };
        for group in groups {
            let depth = group
                .iter()
                .flat_map(|i| edges.get(*i).into_iter().flatten().map(move |c| (*i, *c)))
                .filter_map(|(i, c)| {
                    layer
                        .get(&c)
                        .map(|l| l + usize::from(module_of(i) != module_of(c)))
                })
                .max()
                .unwrap_or(0);
            for i in group {
                layer.insert(i, depth);
            }
        }
    }
    for group in graph::components(&module_edges) {
        let lone = group.len() == 1;
        let mut parts: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
        for (i, _) in sel.owned.iter().enumerate() {
            if let Some(m) = module_of(i).filter(|m| group.contains(m)) {
                let l = if lone {
                    0
                } else {
                    layer.get(&i).copied().unwrap_or(0)
                };
                parts.entry((l, m)).or_default().push(i);
            }
        }
        let mut count: BTreeMap<usize, usize> = BTreeMap::new();
        for ((_, m), members) in parts {
            let n = count.entry(m).or_default();
            *n += 1;
            let name = modules.get(m).copied().unwrap_or("");
            w.files.push(if *n == 1 {
                name.to_owned()
            } else {
                format!("{name}.Part{n}")
            });
            for o in members.iter().filter_map(|i| sel.owned.get(*i)) {
                w.place.insert(o.key.clone(), w.files.len() - 1);
            }
        }
    }
}

/// Every function whose address is taken anywhere in the selection, by
/// the number of its parameters: a key for a function of the selection, a
/// C name otherwise. A call through a pointer reaches one of these or is
/// `unsupported` in the emitted code.
fn addresses(sel: &Selection, w: &World) -> BTreeMap<usize, BTreeSet<String>> {
    let mut out: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    for (ti, unit) in sel.units.iter().enumerate() {
        let mut found = BTreeSet::new();
        for f in &unit.tu.functions {
            order::for_each_expr(&f.body, &mut |e| {
                if let crate::ir::ExprKind::Call {
                    callee,
                    direct: None,
                    ..
                } = &e.kind
                {
                    order::addresses_taken(callee, &mut found);
                }
            });
            let mut top = Vec::new();
            collect_full(&f.body, &mut top);
            for e in top {
                order::addresses_taken(e, &mut found);
            }
        }
        for g in unit.tu.globals.values() {
            if let Some(e) = &g.init {
                order::addresses_taken(e, &mut found);
            }
        }
        for (name, arity) in found {
            let key = sel
                .local_fns
                .get(ti)
                .and_then(|m| m.get(&name))
                .or_else(|| w.external_defs.get(&name))
                .cloned()
                .unwrap_or(name);
            out.entry(arity).or_default().insert(key);
        }
    }
    out
}

/// The full expressions of a statement, outermost only.
fn collect_full<'a>(s: &'a crate::ir::Stmt, out: &mut Vec<&'a crate::ir::Expr>) {
    use crate::ir::{Decl, Stmt};
    match s {
        Stmt::Compound(v) => v.iter().for_each(|s| collect_full(s, out)),
        Stmt::Decl(ds) => {
            for d in ds {
                if let Decl::Var(v) = d
                    && let Some(e) = &v.init
                {
                    out.push(e);
                }
            }
        }
        Stmt::Expr(e) | Stmt::Return(Some(e)) => out.push(e),
        Stmt::If { cond, then, els } => {
            out.push(cond);
            collect_full(then, out);
            if let Some(e) = els {
                collect_full(e, out);
            }
        }
        Stmt::While { cond, body } | Stmt::DoWhile { body, cond } | Stmt::Switch { cond, body } => {
            out.push(cond);
            collect_full(body, out);
        }
        Stmt::For {
            init,
            cond,
            inc,
            body,
        } => {
            if let Some(i) = init {
                collect_full(i, out);
            }
            out.extend([cond, inc].into_iter().flatten().map(|b| &**b));
            collect_full(body, out);
        }
        Stmt::Case { expr, body, .. } => {
            out.push(expr);
            collect_full(body, out);
        }
        Stmt::Default { body } | Stmt::Label { body, .. } => collect_full(body, out),
        _ => {}
    }
}

/// Least fixed point of what each selection function may do to memory its
/// caller can see.
fn summaries(sel: &Selection, w: &World) -> BTreeMap<String, Summary> {
    let mut out: BTreeMap<String, Summary> = sel
        .owned
        .iter()
        .map(|o| (o.key.clone(), Summary::default()))
        .collect();
    loop {
        let mut changed = false;
        for o in &sel.owned {
            let Some(f) = sel.function(o) else { continue };
            let names = sel.local_fns.get(o.tu);
            let key_of = |n: &str| {
                names
                    .and_then(|m| m.get(n))
                    .or_else(|| w.external_defs.get(n))
                    .cloned()
            };
            let cs = |e: &crate::ir::Expr| match world::call_effect(
                e,
                &key_of,
                &|k| out.get(k).copied(),
                &w.addr_taken,
            ) {
                order::CallEffect::Known(s) => s,
                order::CallEffect::External => Summary::WRITES,
            };
            let s = order::summary(f, &cs);
            let old = out.get(&o.key).copied().unwrap_or_default();
            if old.join(s) != old {
                out.insert(o.key.clone(), old.join(s));
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
    /// The Lean file the definition is written to.
    pub(crate) lean_file: String,
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
        let (Some(unit), Some(module)) = (sel.unit(ti), sel.main_module.get(ti)) else {
            continue;
        };
        let mut em = FnEmitter::new(&unit, w, module, "", "");
        for g in unit
            .tu
            .globals
            .values()
            .filter(|g| g.storage != Storage::Extern)
        {
            let Some(key) = unit.globals.get(&g.name) else {
                continue;
            };
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
        let (Some(f), Some(unit)) = (sel.function(o), sel.unit(o.tu)) else {
            continue;
        };
        let em = FnEmitter::new(&unit, w, &o.module, &o.key, &f.name);
        let (mut res, params, sig) = em.function(f);
        if let Some(c) = &o.conflict {
            res.reasons.push(c.clone());
        }
        rows.push(Row {
            key: o.key.clone(),
            module: o.module.clone(),
            lean_file: w
                .place
                .get(&o.key)
                .and_then(|i| w.files.get(*i))
                .cloned()
                .unwrap_or_else(|| o.module.clone()),
            name: f.name.clone(),
            file: f
                .loc
                .as_ref()
                .map_or_else(|| f.def_file.clone(), |l| l.file.clone()),
            line: f.loc.as_ref().map_or(0, |l| l.line),
            origin: f.origin,
            params,
            sig,
            res,
        });
    }
    rows
}

/// External functions, models and assumptions of one function.
type Needs = (BTreeSet<String>, BTreeSet<String>, BTreeSet<String>);

/// What each emitted function needs through the functions it calls.
fn close(rows: &mut [Row]) {
    loop {
        let mut changed = false;
        let snapshot: BTreeMap<String, Needs> = rows
            .iter()
            .map(|r| {
                (
                    r.key.clone(),
                    (
                        r.res.exts.clone(),
                        r.res.models.clone(),
                        r.res.assumptions.clone(),
                    ),
                )
            })
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

/// Everything emission computes, before anything is written: the IR of
/// the selection, what each name means, and the result per function.
pub(crate) struct Analysis {
    sel: Selection,
    pub(crate) world: World,
    pub(crate) rows: Vec<Row>,
}

impl Analysis {
    /// The IR of a row's function, its translation unit with the layouts
    /// clang gave for it, and the path of that unit's main file.
    pub(crate) fn function(&self, key: &str) -> Option<(&Function, &TranslationUnit, &Layouts)> {
        let o = self.sel.owned.iter().find(|o| o.key == key)?;
        let l = self.sel.units.get(o.tu)?;
        Some((l.tu.functions.get(o.index)?, &l.tu, &l.lay))
    }

    /// Index of the translation unit a function was read from, in the
    /// order of the entries given to [`analyse`].
    pub(crate) fn unit_of(&self, key: &str) -> Option<usize> {
        self.sel.owned.iter().find(|o| o.key == key).map(|o| o.tu)
    }

    /// The key a function name has when used from the unit of `from`.
    pub(crate) fn resolve(&self, from: &str, name: &str) -> Option<String> {
        let ti = self.unit_of(from)?;
        self.sel
            .local_fns
            .get(ti)?
            .get(name)
            .or_else(|| self.world.external_defs.get(name))
            .cloned()
    }
}

pub(crate) fn analyse(entries: &[&Entry]) -> Result<Analysis> {
    let units = entries
        .iter()
        .map(|e| load(e))
        .collect::<Result<Vec<_>>>()?;
    let sel = select(units, entries);
    let mut w = prepare(&sel);
    for o in &sel.owned {
        if let (Some(f), Some(unit)) = (sel.function(o), sel.unit(o.tu)) {
            let sig = FnEmitter::new(&unit, &mut w, &o.module, &o.key, &f.name).signature(f);
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
        w.refused = rows
            .iter()
            .filter(|r| !r.res.reasons.is_empty())
            .map(|r| r.key.clone())
            .collect();
        if before == (w.refused.clone(), w.addressed.clone()) {
            break;
        }
    }
    close(&mut rows);
    Ok(Analysis {
        sel,
        world: w,
        rows,
    })
}

pub(crate) fn run(entries: &[&Entry], opts: &Options) -> Result<String> {
    let a = analyse(entries)?;
    project::write(opts, &a.world, &a.rows)?;
    Ok(project::summary(&a.world, &a.rows))
}
