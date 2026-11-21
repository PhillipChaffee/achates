//! Widths of the scalar types, read from the macros clang predefines for the
//! entry's own flags, so no width table is written by hand.

use std::collections::HashMap;

use anyhow::{Context as _, Result};

use crate::clang;
use crate::compdb::{ClangArgs, Entry};

#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq)]
pub(crate) struct Target {
    pub(crate) char_bits: u32,
    pub(crate) char_signed: bool,
    pub(crate) short_bits: u32,
    pub(crate) int_bits: u32,
    pub(crate) long_bits: u32,
    pub(crate) long_long_bits: u32,
    /// `None` when the target has no `__int128`.
    pub(crate) int128_bits: Option<u32>,
    pub(crate) bool_bits: u32,
    pub(crate) pointer_bits: u32,
    pub(crate) float_bits: u32,
    pub(crate) double_bits: u32,
}

pub(crate) fn query(entry: &Entry, args: &ClangArgs) -> Result<Target> {
    let mut cmd = args.flags.clone();
    cmd.extend(["-dM", "-E", "-x", "c", "/dev/null"].map(String::from));
    let out = clang::run(entry, &cmd, "predefined macros")?;
    from_macros(&String::from_utf8_lossy(&out))
        .with_context(|| format!("reading target widths for {}", entry.file))
}

pub(crate) fn from_macros(text: &str) -> Result<Target> {
    let defs: HashMap<&str, &str> = text
        .lines()
        .filter_map(|l| {
            let rest = l.strip_prefix("#define ")?;
            let (name, value) = rest.split_once(' ').unwrap_or((rest, ""));
            Some((name, value))
        })
        .collect();
    let num = |name: &str| -> Result<u32> {
        defs.get(name)
            .with_context(|| format!("clang does not define {name}"))?
            .parse::<u32>()
            .with_context(|| format!("{name} is not a number"))
    };
    let char_bits = num("__CHAR_BIT__")?;
    let bytes = |name: &str| -> Result<u32> { Ok(num(name)? * char_bits) };
    Ok(Target {
        char_bits,
        char_signed: !defs.contains_key("__CHAR_UNSIGNED__"),
        short_bits: num("__SHRT_WIDTH__")?,
        int_bits: num("__INT_WIDTH__")?,
        long_bits: num("__LONG_WIDTH__")?,
        long_long_bits: num("__LLONG_WIDTH__")?,
        int128_bits: if defs.contains_key("__SIZEOF_INT128__") {
            Some(bytes("__SIZEOF_INT128__")?)
        } else {
            None
        },
        bool_bits: num("__BOOL_WIDTH__")?,
        pointer_bits: num("__POINTER_WIDTH__")?,
        float_bits: bytes("__SIZEOF_FLOAT__")?,
        double_bits: bytes("__SIZEOF_DOUBLE__")?,
    })
}
