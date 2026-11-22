//! What one function's emission needs to know about everything else: the
//! other functions of the selection, the modelled and external functions,
//! and the objects with static storage.

use std::collections::{BTreeMap, BTreeSet};

use crate::emit::layout::Layouts;
use crate::emit::names::Sig;
use crate::emit::order::{CallEffect, Summary, call_arity};
use crate::ir::TranslationUnit;
use crate::ir::{Expr, ExprKind};

/// A C library function the Lean runtime models.
#[derive(Debug)]
pub(crate) struct Model {
    pub(crate) name: &'static str,
    pub(crate) lean: &'static str,
    /// The Lean type the model has; a C declaration that maps to another
    /// type is not this function, and stays external.
    pub(crate) sig: &'static str,
    pub(crate) effect: Eff,
    pub(crate) assumes: &'static [&'static str],
}

/// What a modelled function does to memory that existed before the call,
/// which is what the evaluation-order analysis needs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Eff {
    /// Reads memory and writes none.
    Reads,
    /// Reads memory, and writes only objects it allocates, which outlive it.
    Allocates,
    /// May write memory that existed before the call.
    Writes,
}

impl Eff {
    pub(crate) const fn summary(self) -> Summary {
        Summary {
            writes: matches!(self, Self::Writes),
            allocates: matches!(self, Self::Allocates),
            relies: false,
        }
    }
}

pub(crate) const ALLOC: &str = "alloc-succeeds: allocation never returns null; a request of 2^26 bytes or more fails as unsupported";
pub(crate) const CMP: &str = "cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign";
pub(crate) const TALLOC: &str = "talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported";
pub(crate) const ATOMIC: &str =
    "sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs";
pub(crate) const SIGNED_ZERO: &str = "signed-zeros: compiled with -fno-signed-zeros, so the compiled C may differ from this definition in the sign of a zero";

pub(crate) const BLOCK_ORDER: &str = "block-numbering: where C leaves the order of two operands open and both create objects, the two orders give the new objects different block numbers; nothing in the model reads a block number (pointers into different objects are unequal, ordering them is undefined, converting one to an integer is unsupported), so either order gives the same results up to the numbering; operands are evaluated left to right";

pub(crate) const EXT_READS: &str = "external-reads: strncasecmp, strcasecmp and memrchr, taken as parameters, write no memory, as POSIX and glibc specify them; where C leaves the order of a call that reaches one of them and another operand open, the definition relies on this";

/// External functions taken as parameters whose specification says they
/// write no memory. The order analysis treats a call of one as a read,
/// under `EXT_READS`.
pub(crate) const READ_ONLY_EXTERNALS: &[&str] = &["strncasecmp", "strcasecmp", "memrchr"];

/// Compiler builtins that touch no memory.
const PURE_BUILTINS: &[&str] = &[
    "__builtin_expect",
    "__builtin_unreachable",
    "__builtin_isfinite",
    "__builtin_isnan",
];

/// What a function outside the selection, or a builtin, may do.
fn outside_effect(name: &str) -> CallEffect {
    let model = MODELS.iter().find(|m| m.name == name);
    if let Some(m) = model {
        return CallEffect::Known(m.effect.summary());
    }
    if READ_ONLY_EXTERNALS.contains(&name) {
        CallEffect::Known(Summary {
            relies: true,
            ..Summary::default()
        })
    } else if PURE_BUILTINS.contains(&name) {
        CallEffect::Known(Summary::default())
    } else if name.starts_with("__builtin_") {
        CallEffect::Known(Summary::WRITES)
    } else {
        CallEffect::External
    }
}

/// What the call expression `e` may do to memory its caller sees. `key_of`
/// resolves a C name to a selection key where the name means a selection
/// function; `summary` gives that function's summary. A call through a
/// pointer may reach any function whose address is taken with that number
/// of parameters, and does whatever the worst of them does.
pub(crate) fn call_effect(
    e: &Expr,
    key_of: &dyn Fn(&str) -> Option<String>,
    summary: &dyn Fn(&str) -> Option<Summary>,
    addr_taken: &BTreeMap<usize, BTreeSet<String>>,
) -> CallEffect {
    let ExprKind::Call { callee, direct, .. } = &e.kind else {
        return CallEffect::Known(Summary::WRITES);
    };
    let by_name = |n: &str| {
        key_of(n).map_or_else(
            || outside_effect(n),
            |k| CallEffect::Known(summary(&k).unwrap_or(Summary::WRITES)),
        )
    };
    if let Some(n) = direct {
        return by_name(n);
    }
    let Some(targets) = call_arity(callee).and_then(|a| addr_taken.get(&a)) else {
        return CallEffect::Known(Summary::default());
    };
    let mut all = Summary::default();
    for t in targets {
        // A target is a selection key or a C name outside the selection.
        let eff = summary(t).map_or_else(|| outside_effect(t), CallEffect::Known);
        match eff {
            CallEffect::Known(s) => all = all.join(s),
            CallEffect::External => return CallEffect::External,
        }
    }
    CallEffect::Known(all)
}

pub(crate) const EXT_ORDER: &str = "external-order: where C leaves the order of two operands open and one calls a function taken as a parameter while the other reads memory, that function does not write what the other reads; operands are evaluated left to right";

const fn model(
    name: &'static str,
    lean: &'static str,
    sig: &'static str,
    effect: Eff,
    assumes: &'static [&'static str],
) -> Model {
    Model {
        name,
        lean,
        sig,
        effect,
        assumes,
    }
}

pub(crate) const MODELS: &[Model] = &[
    model(
        "__assert_fail",
        "Libc.«__assert_fail»",
        "Ptr → Ptr → U32 → Ptr → M Unit",
        Eff::Reads,
        &[],
    ),
    model("abort", "Libc.abort", "M Unit", Eff::Reads, &[]),
    model(
        "memcpy",
        "Libc.memcpy",
        "Ptr → Ptr → U64 → M Ptr",
        Eff::Writes,
        &[],
    ),
    model(
        "memmove",
        "Libc.memmove",
        "Ptr → Ptr → U64 → M Ptr",
        Eff::Writes,
        &[],
    ),
    model(
        "memset",
        "Libc.memset",
        "Ptr → I32 → U64 → M Ptr",
        Eff::Writes,
        &[],
    ),
    model(
        "memcmp",
        "Libc.memcmp",
        "Ptr → Ptr → U64 → M I32",
        Eff::Reads,
        &[CMP],
    ),
    model(
        "memchr",
        "Libc.memchr",
        "Ptr → I32 → U64 → M Ptr",
        Eff::Reads,
        &[],
    ),
    model("strlen", "Libc.strlen", "Ptr → M U64", Eff::Reads, &[]),
    model(
        "strcmp",
        "Libc.strcmp",
        "Ptr → Ptr → M I32",
        Eff::Reads,
        &[CMP],
    ),
    model(
        "strncmp",
        "Libc.strncmp",
        "Ptr → Ptr → U64 → M I32",
        Eff::Reads,
        &[CMP],
    ),
    model(
        "strchr",
        "Libc.strchr",
        "Ptr → I32 → M Ptr",
        Eff::Reads,
        &[],
    ),
    model(
        "malloc",
        "Libc.malloc",
        "U64 → M Ptr",
        Eff::Allocates,
        &[ALLOC],
    ),
    model(
        "calloc",
        "Libc.calloc",
        "U64 → U64 → M Ptr",
        Eff::Allocates,
        &[ALLOC],
    ),
    model("free", "Libc.free", "Ptr → M Unit", Eff::Writes, &[]),
    model(
        "ta_alloc_size",
        "Talloc.ta_alloc_size",
        "Ptr → U64 → M Ptr",
        Eff::Allocates,
        &[ALLOC, TALLOC],
    ),
    model(
        "ta_zalloc_size",
        "Talloc.ta_zalloc_size",
        "Ptr → U64 → M Ptr",
        Eff::Allocates,
        &[ALLOC, TALLOC],
    ),
    model(
        "ta_new_context",
        "Talloc.ta_new_context",
        "Ptr → M Ptr",
        Eff::Allocates,
        &[ALLOC, TALLOC],
    ),
    model(
        "ta_realloc_size",
        "Talloc.ta_realloc_size",
        "Ptr → Ptr → U64 → M Ptr",
        Eff::Writes,
        &[ALLOC, TALLOC],
    ),
    model(
        "ta_xrealloc_size",
        "Talloc.ta_xrealloc_size",
        "Ptr → Ptr → U64 → M Ptr",
        Eff::Writes,
        &[ALLOC, TALLOC],
    ),
    model(
        "ta_free",
        "Talloc.ta_free",
        "Ptr → M Unit",
        Eff::Writes,
        &[TALLOC],
    ),
    model(
        "ta_free_children",
        "Talloc.ta_free_children",
        "Ptr → M Unit",
        Eff::Writes,
        &[TALLOC],
    ),
    model(
        "ta_get_size",
        "Talloc.ta_get_size",
        "Ptr → M U64",
        Eff::Reads,
        &[TALLOC],
    ),
    model(
        "ta_set_destructor",
        "Talloc.ta_set_destructor",
        "Ptr → Ptr → M Unit",
        Eff::Writes,
        &[TALLOC],
    ),
    model(
        "ta_set_parent",
        "Talloc.ta_set_parent",
        "Ptr → Ptr → M Unit",
        Eff::Writes,
        &[TALLOC],
    ),
    model(
        "ta_steal_",
        "Talloc.ta_steal_",
        "Ptr → Ptr → M Ptr",
        Eff::Writes,
        &[TALLOC],
    ),
    model(
        "ta_dbg_set_loc",
        "Talloc.ta_dbg_set_loc",
        "Ptr → Ptr → M Ptr",
        Eff::Reads,
        &[TALLOC],
    ),
    model(
        "ta_calc_array_size",
        "Talloc.ta_calc_array_size",
        "U64 → U64 → M U64",
        Eff::Reads,
        &[],
    ),
    model(
        "ta_calc_prealloc_elems",
        "Talloc.ta_calc_prealloc_elems",
        "U64 → M U64",
        Eff::Reads,
        &[],
    ),
    model(
        "ta_xstrndup",
        "Talloc.ta_xstrndup",
        "Ptr → Ptr → U64 → M Ptr",
        Eff::Allocates,
        &[ALLOC, TALLOC],
    ),
    model(
        "ta_xstrdup",
        "Talloc.ta_xstrdup",
        "Ptr → Ptr → M Ptr",
        Eff::Allocates,
        &[ALLOC, TALLOC],
    ),
];

/// A function defined in the selection.
#[derive(Debug, Clone)]
pub(crate) struct FnMeta {
    /// Unique across the selection: the C name, prefixed by the module for
    /// a function with internal linkage. Also the name its address carries.
    pub(crate) key: String,
    pub(crate) module: String,
    pub(crate) name: String,
    pub(crate) sig: Result<Sig, String>,
}

/// What a function name means at a place where it is used.
#[derive(Debug)]
pub(crate) enum Target<'w> {
    /// Emitted in a module the user's module can import.
    Emitted(&'w FnMeta),
    Model(&'static Model),
    /// A parameter of the emitted code, by the name of its class.
    Ext(String),
}

#[derive(Debug)]
pub(crate) enum StaticBlock {
    Str {
        bytes: Vec<u8>,
        size: u64,
    },
    Obj {
        lean: String,
        size: u64,
        align: u64,
        readonly: bool,
        what: String,
    },
}

#[derive(Debug, Default)]
pub(crate) struct Statics {
    pub(crate) blocks: Vec<StaticBlock>,
    strings: BTreeMap<(Vec<u8>, u64), usize>,
    /// Global key to block number, or why the object cannot be emitted.
    pub(crate) globals: BTreeMap<String, Result<usize, String>>,
    /// Initialisation code, one definition per object.
    pub(crate) inits: Vec<(usize, Vec<String>)>,
}

impl Statics {
    pub(crate) fn string(&mut self, bytes: &[u8], size: u64) -> String {
        let n = self.blocks.len();
        let id = *self.strings.entry((bytes.to_vec(), size)).or_insert(n);
        if id == n {
            self.blocks.push(StaticBlock::Str {
                bytes: bytes.to_vec(),
                size,
            });
        }
        format!("Statics.str_{id}")
    }

    pub(crate) fn object(
        &mut self,
        key: &str,
        lean: String,
        size: u64,
        align: u64,
        readonly: bool,
    ) -> usize {
        let id = self.blocks.len();
        self.blocks.push(StaticBlock::Obj {
            lean,
            size,
            align,
            readonly,
            what: key.to_owned(),
        });
        self.globals.insert(key.to_owned(), Ok(id));
        id
    }

    /// The Lean term for the address of a registered object.
    pub(crate) fn term(&self, key: &str) -> Result<String, String> {
        match self.globals.get(key) {
            Some(Ok(id)) => match self.blocks.get(*id) {
                Some(StaticBlock::Obj { lean, .. }) => Ok(format!("Statics.{lean}")),
                _ => Err("no storage".into()),
            },
            Some(Err(e)) => Err(e.clone()),
            None => Err("not defined in the selection".into()),
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct World {
    pub(crate) fns: BTreeMap<String, FnMeta>,
    /// Functions with external linkage defined in the selection, by C name.
    pub(crate) external_defs: BTreeMap<String, String>,
    /// Keys of functions found not emittable in an earlier round.
    pub(crate) refused: BTreeSet<String>,
    /// The Lean file each function is written to, as an index into
    /// `files`, which is in import order.
    pub(crate) place: BTreeMap<String, usize>,
    pub(crate) files: Vec<String>,
    /// External classes: name to Lean type, or the conflict found.
    pub(crate) exts: BTreeMap<String, Result<String, String>>,
    /// Every function whose address is taken somewhere, as its address
    /// names it, with what the name means from the taking unit.
    pub(crate) addressed: BTreeMap<String, Option<Sig>>,
    /// What each selection function may do to memory its caller sees.
    pub(crate) summaries: BTreeMap<String, Summary>,
    /// Functions whose address is taken, by number of parameters.
    pub(crate) addr_taken: BTreeMap<usize, BTreeSet<String>>,
    pub(crate) statics: Statics,
}

impl World {
    /// Whether the file of `from` can import the file of `to`.
    pub(crate) fn importable(&self, from: &str, to: &str) -> bool {
        match (self.place.get(from), self.place.get(to)) {
            (Some(a), Some(b)) => b <= a,
            _ => false,
        }
    }

    /// Registers a use of an external function and returns its class name.
    pub(crate) fn ext(&mut self, name: &str, sig: &Sig) -> Result<String, String> {
        let arrow = sig.arrow();
        let class = format!("Ext.{}", crate::emit::names::ident(&name.replace('.', "_")));
        match self.exts.get(name) {
            None => {
                self.exts.insert(name.to_owned(), Ok(arrow));
            }
            Some(Ok(a)) if *a == arrow => {}
            Some(Ok(a)) => {
                let msg = format!("`{name}` is declared with two types: {a} and {arrow}");
                self.exts.insert(name.to_owned(), Err(msg));
            }
            Some(Err(_)) => {}
        }
        match self.exts.get(name) {
            Some(Err(e)) => Err(e.clone()),
            _ => Ok(class),
        }
    }
}

/// One translation unit, as functions defined in it see the world.
#[derive(Debug)]
pub(crate) struct Unit<'a> {
    pub(crate) tu: &'a TranslationUnit,
    pub(crate) lay: &'a Layouts,
    /// Function name to key, for the functions this unit defines.
    pub(crate) local_fns: BTreeMap<String, String>,
    /// Global name to key, for objects the selection defines.
    pub(crate) globals: BTreeMap<String, String>,
    /// Compiler flags of this unit that change floating-point results.
    pub(crate) float_flags: Vec<String>,
}

impl Unit<'_> {
    pub(crate) fn fn_key<'s>(&'s self, w: &'s World, name: &str) -> Option<&'s String> {
        self.local_fns
            .get(name)
            .or_else(|| w.external_defs.get(name))
    }

    pub(crate) fn target<'w>(&self, w: &'w World, name: &str, from: &str) -> Target<'w> {
        if let Some(meta) = self.fn_key(w, name).and_then(|k| w.fns.get(k)) {
            return if !w.refused.contains(&meta.key) && w.importable(from, &meta.key) {
                Target::Emitted(meta)
            } else {
                Target::Ext(meta.key.clone())
            };
        }
        MODELS
            .iter()
            .find(|m| m.name == name)
            .map_or_else(|| Target::Ext(name.to_owned()), Target::Model)
    }
}
