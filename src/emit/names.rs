//! Lean names for C names, and Lean types for C types.

use crate::types::{FloatKind, IntType};

/// Lean keywords and the runtime names emitted code refers to: a C
/// identifier spelt like one of these is written differently.
const RESERVED: &[&str] = &[
    "abbrev", "at", "axiom", "break", "by", "calc", "catch", "class", "continue", "def",
    "default", "deriving", "do", "else", "end", "example", "export", "extends", "finally", "for",
    "from", "fun", "have", "if", "import", "in", "inductive", "infix", "instance", "let",
    "local", "macro", "match", "mut", "mutual", "namespace", "notation", "nomatch", "of", "open",
    "partial", "prefix", "private", "protected", "pure", "return", "section", "set_option",
    "show", "structure", "suffices", "syntax", "then", "theorem", "try", "universe", "unless",
    "unsafe", "using", "variable", "where", "with", "fuel", "decide", "ub", "unsupported", "not",
    "true", "false", "throw", "get", "set", "modify", "discard", "id", "Type", "Prop", "Sort",
];

fn is_plain(name: &str) -> bool {
    let mut cs = name.chars();
    cs.next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && cs.all(|c| c.is_ascii_alphanumeric() || c == '_')
        && name != "_"
}

/// A C identifier as a Lean identifier that names a definition.
pub(crate) fn ident(name: &str) -> String {
    if is_plain(name) && !RESERVED.contains(&name) && !name.starts_with("__") {
        name.to_owned()
    } else {
        format!("«{name}»")
    }
}

/// A C variable as a Lean local: never a keyword, and never a name the
/// runtime uses (those start with a capital or are reserved above).
pub(crate) fn local(name: &str) -> String {
    let plain = is_plain(name);
    let clash = RESERVED.contains(&name)
        || name.chars().next().is_some_and(|c| c.is_ascii_uppercase() || c == '_')
        || name
            .strip_prefix(['t', 'j'])
            .is_some_and(|r| !r.is_empty() && r.chars().all(|c| c.is_ascii_digit()));
    if plain && !clash {
        name.to_owned()
    } else {
        let safe: String = name
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        format!("v_{safe}")
    }
}

/// A path component as part of a Lean module name: `bstr.c` gives `Bstr_c`.
pub(crate) fn module_part(s: &str) -> String {
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        let c = if c.is_ascii_alphanumeric() { c } else { '_' };
        if i == 0 {
            if c.is_ascii_digit() || c == '_' {
                out.push('M');
            }
            out.push(c.to_ascii_uppercase());
        } else {
            out.push(c);
        }
    }
    out
}

pub(crate) fn int_ty(i: IntType) -> String {
    format!("{}{}", if i.signed { 'I' } else { 'U' }, i.bits)
}

pub(crate) const fn int_ns(i: IntType) -> &'static str {
    if i.signed { "SInt" } else { "UInt" }
}

pub(crate) const fn float_ty(k: FloatKind) -> &'static str {
    match k {
        FloatKind::Float => "F32",
        FloatKind::Double => "F64",
    }
}

/// The Lean shape of a C function type: parameter types, whether more
/// arguments may follow, and the result type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Sig {
    pub(crate) params: Vec<String>,
    pub(crate) variadic: bool,
    pub(crate) ret: String,
}

impl Sig {
    /// As a Lean type, without the fuel argument.
    pub(crate) fn arrow(&self) -> String {
        let mut s = String::new();
        for p in &self.params {
            s.push_str(p);
            s.push_str(" → ");
        }
        if self.variadic {
            s.push_str("List VArg → ");
        }
        s.push_str("M ");
        s.push_str(&self.ret);
        s
    }
}
