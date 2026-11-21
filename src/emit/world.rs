//! What one function's emission needs to know about everything else: the
//! other functions of the selection, the modelled and external functions,
//! and the objects with static storage.

use std::collections::{BTreeMap, BTreeSet};

use crate::emit::layout::Layouts;
use crate::emit::names::Sig;
use crate::ir::TranslationUnit;

/// A C library function the Lean runtime models.
#[derive(Debug)]
pub(crate) struct Model {
    pub(crate) name: &'static str,
    pub(crate) lean: &'static str,
    /// The Lean type the model has; a C declaration that maps to another
    /// type is not this function, and stays external.
    pub(crate) sig: &'static str,
    pub(crate) writes: bool,
    pub(crate) assumes: &'static [&'static str],
}

pub(crate) const ALLOC: &str =
    "alloc-succeeds: allocation never returns null; a request of 2^47 bytes or more fails as unsupported";
pub(crate) const CMP: &str = "cmp-byte-difference: memcmp, strcmp and strncmp return the difference of the first differing bytes, as glibc does on x86-64; C fixes only the sign";
pub(crate) const TALLOC: &str = "talloc-model: talloc is modelled as allocate and free with parent ownership; freeing an allocation that has a destructor fails as unsupported";
pub(crate) const ATOMIC: &str =
    "sequential-atomics: atomic loads and stores are plain loads and stores; no other thread runs";
pub(crate) const SIGNED_ZERO: &str = "signed-zeros: compiled with -fno-signed-zeros, so the compiled C may differ from this definition in the sign of a zero";

const fn model(
    name: &'static str,
    lean: &'static str,
    sig: &'static str,
    writes: bool,
    assumes: &'static [&'static str],
) -> Model {
    Model {
        name,
        lean,
        sig,
        writes,
        assumes,
    }
}

pub(crate) const MODELS: &[Model] = &[
    model("__assert_fail", "Libc.«__assert_fail»", "Ptr → Ptr → U32 → Ptr → M Unit", false, &[]),
    model("abort", "Libc.abort", "M Unit", false, &[]),
    model("memcpy", "Libc.memcpy", "Ptr → Ptr → U64 → M Ptr", true, &[]),
    model("memmove", "Libc.memmove", "Ptr → Ptr → U64 → M Ptr", true, &[]),
    model("memset", "Libc.memset", "Ptr → I32 → U64 → M Ptr", true, &[]),
    model("memcmp", "Libc.memcmp", "Ptr → Ptr → U64 → M I32", false, &[CMP]),
    model("memchr", "Libc.memchr", "Ptr → I32 → U64 → M Ptr", false, &[]),
    model("strlen", "Libc.strlen", "Ptr → M U64", false, &[]),
    model("strcmp", "Libc.strcmp", "Ptr → Ptr → M I32", false, &[CMP]),
    model("strncmp", "Libc.strncmp", "Ptr → Ptr → U64 → M I32", false, &[CMP]),
    model("strchr", "Libc.strchr", "Ptr → I32 → M Ptr", false, &[]),
    model("malloc", "Libc.malloc", "U64 → M Ptr", true, &[ALLOC]),
    model("calloc", "Libc.calloc", "U64 → U64 → M Ptr", true, &[ALLOC]),
    model("free", "Libc.free", "Ptr → M Unit", true, &[]),
    model("ta_alloc_size", "Talloc.ta_alloc_size", "Ptr → U64 → M Ptr", true, &[ALLOC, TALLOC]),
    model("ta_zalloc_size", "Talloc.ta_zalloc_size", "Ptr → U64 → M Ptr", true, &[ALLOC, TALLOC]),
    model("ta_new_context", "Talloc.ta_new_context", "Ptr → M Ptr", true, &[ALLOC, TALLOC]),
    model("ta_realloc_size", "Talloc.ta_realloc_size", "Ptr → Ptr → U64 → M Ptr", true, &[ALLOC, TALLOC]),
    model("ta_xrealloc_size", "Talloc.ta_xrealloc_size", "Ptr → Ptr → U64 → M Ptr", true, &[ALLOC, TALLOC]),
    model("ta_free", "Talloc.ta_free", "Ptr → M Unit", true, &[TALLOC]),
    model("ta_free_children", "Talloc.ta_free_children", "Ptr → M Unit", true, &[TALLOC]),
    model("ta_get_size", "Talloc.ta_get_size", "Ptr → M U64", false, &[TALLOC]),
    model("ta_set_destructor", "Talloc.ta_set_destructor", "Ptr → Ptr → M Unit", true, &[TALLOC]),
    model("ta_set_parent", "Talloc.ta_set_parent", "Ptr → Ptr → M Unit", true, &[TALLOC]),
    model("ta_steal_", "Talloc.ta_steal_", "Ptr → Ptr → M Ptr", true, &[TALLOC]),
    model("ta_dbg_set_loc", "Talloc.ta_dbg_set_loc", "Ptr → Ptr → M Ptr", false, &[TALLOC]),
    model("ta_calc_array_size", "Talloc.ta_calc_array_size", "U64 → U64 → M U64", false, &[]),
    model("ta_calc_prealloc_elems", "Talloc.ta_calc_prealloc_elems", "U64 → M U64", false, &[]),
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
    Str { bytes: Vec<u8>, size: u64 },
    Obj { lean: String, size: u64, align: u64, readonly: bool, what: String },
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

    pub(crate) fn object(&mut self, key: &str, lean: String, size: u64, align: u64, readonly: bool) -> usize {
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
    /// Position of each module in import order.
    pub(crate) module_pos: BTreeMap<String, usize>,
    /// External classes: name to Lean type, or the conflict found.
    pub(crate) exts: BTreeMap<String, Result<String, String>>,
    /// Every function whose address is taken somewhere, as its address
    /// names it, with what the name means from the taking unit.
    pub(crate) addressed: BTreeMap<String, Option<Sig>>,
    /// Whether each selection function may write memory its caller sees.
    pub(crate) writes: BTreeMap<String, bool>,
    pub(crate) statics: Statics,
}

impl World {
    pub(crate) fn importable(&self, from: &str, to: &str) -> bool {
        from == to
            || match (self.module_pos.get(from), self.module_pos.get(to)) {
                (Some(a), Some(b)) => b < a,
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
        self.local_fns.get(name).or_else(|| w.external_defs.get(name))
    }

    pub(crate) fn target<'w>(&self, w: &'w World, name: &str, from: &str) -> Target<'w> {
        if let Some(meta) = self.fn_key(w, name).and_then(|k| w.fns.get(k)) {
            return if !w.refused.contains(&meta.key) && w.importable(from, &meta.module) {
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
