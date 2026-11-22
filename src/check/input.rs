//! Test inputs: one line of tokens per call, made from the shapes of the
//! parameters by a generator with a fixed seed.
//!
//! Token grammar, shared with the Lean driver and the C harness: an integer
//! is decimal; a float is the hexadecimal bit pattern; a buffer is `N`
//! (null) or `H` followed by hexadecimal bytes, and for a `bstr` optionally
//! `:<k>`, room for `k` more bytes when it is a talloc buffer; a pointer to an object is
//! `N` or `P` followed by the object's tokens; a talloc context is `N` or
//! `C`; a struct is its members in order.

use std::fmt::Write as _;

use crate::check::format;
use crate::check::shape::Shape;
use crate::types::FloatKind;

/// `SplitMix64`: small, and the same on every platform.
#[derive(Debug, Clone)]
pub(crate) struct Rng(u64);

impl Rng {
    pub(crate) fn new(seed: u64, name: &str) -> Self {
        // FNV-1a over the name, so every function has its own stream and
        // adding a function does not change the inputs of another.
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for b in name.bytes() {
            h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
        Self(seed ^ h)
    }

    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n`; 0 when `n` is 0.
    pub(crate) fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }

    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> Option<T> {
        let i = usize::try_from(self.below(items.len() as u64)).ok()?;
        items.get(i).copied()
    }
}

/// Constants of the function under test and of what it calls: inputs built
/// from them reach branches that random bytes almost never do.
#[derive(Debug, Default, Clone)]
pub(crate) struct Dictionary {
    pub(crate) strings: Vec<Vec<u8>>,
    pub(crate) ints: Vec<i128>,
}

/// Bytes that C string code tends to treat specially.
const BYTES: &[u8] =
    b" \t\n\r\0/\\.:%-+_0123456789abcdefABCDEFxX\x7f\x80\xbf\xc2\xc3\xe2\xef\xf0\xf4\xff";

/// Lengths at and around the block sizes of vectorised string functions.
const LENGTHS: &[u64] = &[
    0, 1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129,
];

/// UTF-8 sequences: valid ones of each length, then truncated, overlong,
/// surrogate and out-of-range ones.
const UTF8: &[&[u8]] = &[
    b"a",
    b"\xc3\xa9",
    b"\xe2\x82\xac",
    b"\xf0\x9f\x98\x80",
    b"\xe4\xb8\xad",
    b"\xcc\x81",
    b"\xe2\x80\x8d",
    b"\xef\xbb\xbf",
    b"\xff\xfe",
    b"\xfe\xff",
    b"\xc3",
    b"\xe2\x82",
    b"\xf0\x9f\x98",
    b"\xc0\x80",
    b"\xe0\x80\x80",
    b"\xed\xa0\x80",
    b"\xf4\x90\x80\x80",
    b"\xf8\x88\x80\x80\x80",
    b"\x80",
];

#[derive(Debug)]
pub(crate) struct Gen<'d> {
    rng: Rng,
    dict: &'d Dictionary,
    /// Buffers made earlier for this call, so that a later one can be equal
    /// to one, or a part of one, or differ from one in a single byte.
    made: Vec<Vec<u8>>,
    /// Buffers are mostly number text.
    numeric: bool,
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::from("H");
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

impl<'d> Gen<'d> {
    pub(crate) fn new(seed: u64, name: &str, dict: &'d Dictionary) -> Self {
        Self {
            rng: Rng::new(seed, name),
            dict,
            made: Vec::new(),
            numeric: false,
        }
    }

    fn length(&mut self) -> u64 {
        match self.rng.below(10) {
            0 => 0,
            1..=4 => 1 + self.rng.below(8),
            5..=7 => 9 + self.rng.below(32),
            _ => self.rng.pick(LENGTHS).unwrap_or(0),
        }
    }

    /// Text that number parsers treat specially: blanks, a sign, a base
    /// prefix (`0x`, `0b`, `0`), digits of several bases, and a tail.
    fn number(&mut self) -> Vec<u8> {
        const PREFIX: &[&[u8]] = &[b"", b"0", b"0x", b"0X", b"0b", b"0B", b"00"];
        const DIGITS: &[u8] = b"0123456789abcdefABCDEFxXbB";
        let mut out = Vec::new();
        for _ in 0..self.rng.below(3) {
            out.push(self.rng.pick(b" \t\n").unwrap_or(b' '));
        }
        if self.rng.chance(1, 3) {
            out.push(self.rng.pick(b"+-").unwrap_or(b'-'));
        }
        let prefix = self.rng.pick(PREFIX).unwrap_or(b"");
        out.extend_from_slice(prefix);
        // Mostly digits the prefix announces, so that the prefix is taken.
        let valid: &[u8] = match prefix {
            b"0x" | b"0X" => b"0123456789abcdefABCDEF",
            b"0b" | b"0B" => b"01",
            b"0" | b"00" => b"01234567",
            _ => b"0123456789",
        };
        for _ in 0..self.rng.below(24) {
            let set = if self.rng.chance(7, 8) { valid } else { DIGITS };
            out.push(self.rng.pick(set).unwrap_or(b'0'));
        }
        if self.rng.chance(1, 2) {
            out.push(self.rng.pick(BYTES).unwrap_or(b' '));
        }
        out
    }

    fn fresh_bytes(&mut self) -> Vec<u8> {
        if self.rng.chance(1, if self.numeric { 2 } else { 12 }) {
            return self.number();
        }
        let n = self.length();
        let mode = self.rng.below(6);
        let mut out = Vec::new();
        while (out.len() as u64) < n {
            match mode {
                0 => out.push(self.rng.next().to_le_bytes().first().copied().unwrap_or(0)),
                1 => out.push(0x20 + u8::try_from(self.rng.below(95)).unwrap_or(0)),
                2 => out.push(self.rng.pick(BYTES).unwrap_or(b' ')),
                3 => out.extend_from_slice(self.rng.pick(UTF8).unwrap_or(b"a")),
                _ => {
                    // Words from the function's own constants, joined by
                    // bytes that often separate them.
                    if !self.dict.strings.is_empty() && self.rng.chance(2, 3) {
                        let i = usize::try_from(self.rng.below(self.dict.strings.len() as u64))
                            .unwrap_or(0);
                        out.extend_from_slice(self.dict.strings.get(i).map_or(&[], Vec::as_slice));
                    } else if self.rng.chance(1, 2) {
                        out.push(self.rng.pick(BYTES).unwrap_or(b' '));
                    } else {
                        out.push(b'a' + u8::try_from(self.rng.below(26)).unwrap_or(0));
                    }
                }
            }
        }
        // Whole sequences were appended, so the length may overshoot; an
        // exact boundary length matters more than an unbroken last one.
        if mode != 4 || self.rng.chance(1, 2) {
            out.truncate(usize::try_from(n).unwrap_or(0));
        }
        out
    }

    fn derived(&mut self) -> Option<Vec<u8>> {
        if self.made.is_empty() {
            return None;
        }
        let i = usize::try_from(self.rng.below(self.made.len() as u64)).ok()?;
        let mut b = self.made.get(i)?.clone();
        let len = b.len() as u64;
        match self.rng.below(8) {
            0 => {}
            1 => b.truncate(usize::try_from(self.rng.below(len + 1)).ok()?),
            2 => {
                b.drain(..usize::try_from(self.rng.below(len + 1)).ok()?);
            }
            3 => {
                let from = usize::try_from(self.rng.below(len + 1)).ok()?;
                let to = from + usize::try_from(self.rng.below(len - from as u64 + 1)).ok()?;
                b = b.get(from..to)?.to_vec();
            }
            4 => {
                if let Some(x) = b.get_mut(usize::try_from(self.rng.below(len)).ok()?) {
                    *x = x.wrapping_add(1);
                }
            }
            5 => {
                for x in &mut b {
                    if self.rng.chance(1, 2) {
                        *x = if x.is_ascii_lowercase() {
                            x.to_ascii_uppercase()
                        } else {
                            x.to_ascii_lowercase()
                        };
                    }
                }
            }
            6 => b.push(self.rng.pick(BYTES).unwrap_or(b' ')),
            _ => {
                let extra = self.fresh_bytes();
                b.extend_from_slice(&extra);
            }
        }
        Some(b)
    }

    fn bytes(&mut self, allow_nul: bool) -> Vec<u8> {
        let mut b = if self.rng.chance(1, 3) {
            self.derived().unwrap_or_else(|| self.fresh_bytes())
        } else {
            self.fresh_bytes()
        };
        if !allow_nul {
            b.retain(|x| *x != 0);
        }
        self.made.push(b.clone());
        b
    }

    fn int(&mut self, bits: u32, signed: bool) -> String {
        let mask: u128 = if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        let wrap = |v: i128| -> u128 { v.cast_unsigned() & mask };
        let raw: u128 = match self.rng.below(if bits <= 8 { 2 } else { 10 }) {
            // Every byte value matters for an 8-bit type; draw it uniformly.
            0 if bits <= 8 => u128::from(self.rng.below(256)),
            0..=3 => wrap(i128::from(self.rng.below(74)) - 3),
            4 | 5 => match self.rng.pick(&self.dict.ints) {
                Some(v) => wrap(v + i128::from(self.rng.below(3)) - 1),
                None => wrap(i128::from(self.rng.below(300)) - 20),
            },
            6 => {
                let edge = [0u128, 1, mask, mask >> 1, (mask >> 1) + 1, mask - 1];
                self.rng.pick(&edge).unwrap_or(0)
            }
            7 => {
                let shift = u32::try_from(self.rng.below(u64::from(bits))).unwrap_or(0);
                wrap((1i128 << shift) + i128::from(self.rng.below(3)) - 1)
            }
            _ => (u128::from(self.rng.next()) | (u128::from(self.rng.next()) << 64)) & mask,
        };
        if signed && bits < 128 && raw > (mask >> 1) {
            format!("-{}", mask - raw + 1)
        } else {
            raw.to_string()
        }
    }

    fn float(&mut self, kind: FloatKind) -> String {
        const SPECIAL: &[f64] = &[
            0.0,
            -0.0,
            1.0,
            -1.0,
            0.5,
            2.0,
            1e-3,
            1e9,
            1e18,
            1e19,
            -1e19,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
            f64::MIN_POSITIVE,
            f64::MAX,
            5e-324,
            4_294_967_296.0,
            9_223_372_036_854_775_807.0,
        ];
        let pick = self.rng.below(4);
        if pick == 1 {
            // Random bits of the type itself: a random double rounds to
            // infinity or zero as a float almost always.
            return match kind {
                FloatKind::Double => format!("{:x}", self.rng.next()),
                FloatKind::Float => format!("{:x}", self.rng.next() & 0xffff_ffff),
            };
        }
        let v: f64 = match pick {
            0 => self.rng.pick(SPECIAL).unwrap_or(0.0),
            2 => {
                (f64::from(u32::try_from(self.rng.below(2_000_001)).unwrap_or(0)) - 1_000_000.0)
                    / 1000.0
            }
            _ => (f64::from(u32::try_from(self.rng.below(2001)).unwrap_or(0)) - 1000.0) * 0.25,
        };
        match kind {
            FloatKind::Double => format!("{:x}", v.to_bits()),
            // Through the decimal text, which rounds to nearest as a cast
            // does; `inf`, `-inf` and `NaN` read back as themselves.
            FloatKind::Float => format!(
                "{:x}",
                v.to_string().parse::<f32>().unwrap_or(f32::NAN).to_bits()
            ),
        }
    }

    fn shape(&mut self, s: &Shape, out: &mut Vec<String>) {
        match s {
            Shape::Bool => out.push(self.rng.below(2).to_string()),
            Shape::Int { ty, .. } => out.push(self.int(ty.bits, ty.signed)),
            Shape::Float(k) => out.push(self.float(*k)),
            Shape::Bstr => {
                if self.rng.chance(1, 24) {
                    out.push("N".into());
                } else {
                    let b = self.bytes(true);
                    // Room past the contents matters only to a talloc
                    // buffer (a `bstr` the function may append to), where
                    // mpv's buffers usually have it.
                    let room = if self.rng.chance(1, 2) {
                        format!(":{}", self.rng.pick(&[1, 2, 7, 16, 40]).unwrap_or(1))
                    } else {
                        String::new()
                    };
                    out.push(format!("{}{room}", hex(&b)));
                }
            }
            Shape::CStr => {
                if self.rng.chance(1, 48) {
                    out.push("N".into());
                } else {
                    let b = self.bytes(false);
                    out.push(hex(&b));
                }
            }
            Shape::TallocCtx => out.push(if self.rng.chance(1, 4) { "N" } else { "C" }.into()),
            Shape::StrList { .. } => {
                if self.rng.chance(1, 12) {
                    out.push("N".into());
                } else {
                    let n = self.rng.below(6);
                    out.push(format!("L{n}"));
                    for _ in 0..n {
                        self.shape(&Shape::CStr, out);
                    }
                }
            }
            // Neither takes a token: a slot starts null, and a `va_list`
            // holds the arguments its format read.
            Shape::Slot { .. } | Shape::VaList => {}
            Shape::Struct { fields, .. } => {
                for f in fields {
                    self.shape(&f.shape, out);
                }
            }
            Shape::Array { elem, len, .. } => {
                for _ in 0..*len {
                    self.shape(elem, out);
                }
            }
            Shape::Ptr { pointee, .. } => {
                if self.rng.chance(1, 12) {
                    out.push("N".into());
                } else {
                    out.push("P".into());
                    self.shape(pointee, out);
                }
            }
            Shape::Format(kind) => {
                let formats = kind.formats();
                let k = self.rng.below(formats.len() as u64);
                out.push(format!("F{k}"));
                let fmt = formats
                    .get(usize::try_from(k).unwrap_or(0))
                    .copied()
                    .unwrap_or("");
                match kind {
                    format::Kind::Printf => {
                        for a in format::printf_args(fmt) {
                            self.format_arg(a, out);
                        }
                    }
                    // What each target holds before the call, so that one
                    // the call leaves alone reads the same on both sides.
                    format::Kind::Scanf => {
                        for t in format::scanf_targets(fmt) {
                            let mut b = Vec::new();
                            for _ in 0..t.size {
                                b.push(self.rng.next().to_le_bytes().first().copied().unwrap_or(0));
                            }
                            out.push(hex(&b));
                        }
                    }
                }
            }
        }
    }

    fn format_arg(&mut self, a: format::Arg, out: &mut Vec<String>) {
        match a {
            // Mostly field widths and precisions a terminal would show;
            // sometimes negative, sometimes too large for the model.
            format::Arg::Star => out.push(if self.rng.chance(1, 16) {
                self.int(32, true)
            } else {
                (i64::try_from(self.rng.below(41)).unwrap_or(0) - 10).to_string()
            }),
            format::Arg::Double => out.push(self.float(FloatKind::Double)),
            format::Arg::Str => self.shape(&Shape::CStr, out),
            _ => {
                let (bits, signed) = a.int().unwrap_or((32, true));
                out.push(self.int(bits, signed));
            }
        }
    }

    /// The tokens of one call.
    pub(crate) fn case(&mut self, params: &[(String, Shape)]) -> String {
        self.made.clear();
        // The text a scanf-like function reads is a number half the time.
        self.numeric = params
            .iter()
            .any(|p| p.1 == Shape::Format(format::Kind::Scanf));
        let mut out = Vec::new();
        for (_, s) in params {
            self.shape(s, &mut out);
        }
        out.join(" ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{IntKind, IntType};

    #[test]
    fn the_same_seed_gives_the_same_inputs() {
        let dict = Dictionary::default();
        let params = vec![("s".to_owned(), Shape::Bstr), ("t".to_owned(), Shape::CStr)];
        let a: Vec<String> = {
            let mut g = Gen::new(7, "f", &dict);
            (0..50).map(|_| g.case(&params)).collect()
        };
        let b: Vec<String> = {
            let mut g = Gen::new(7, "f", &dict);
            (0..50).map(|_| g.case(&params)).collect()
        };
        assert_eq!(a, b);
        let mut g = Gen::new(8, "f", &dict);
        let c: Vec<String> = (0..50).map(|_| g.case(&params)).collect();
        assert_ne!(a, c);
    }

    #[test]
    fn buffers_cover_empty_null_high_bytes_and_embedded_nul() {
        let dict = Dictionary::default();
        let params = vec![("s".to_owned(), Shape::Bstr), ("t".to_owned(), Shape::CStr)];
        let mut g = Gen::new(1, "f", &dict);
        let cases: Vec<Vec<String>> = (0..4000)
            .map(|_| g.case(&params).split(' ').map(str::to_owned).collect())
            .collect();
        let bstrs: Vec<&str> = cases.iter().map(|c| c[0].as_str()).collect();
        let cstrs: Vec<&str> = cases.iter().map(|c| c[1].as_str()).collect();
        let bytes = |t: &str| -> Vec<u8> {
            let t = t.split(':').next().unwrap_or("");
            (1..t.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&t[i..i + 2], 16).unwrap())
                .collect()
        };
        assert!(bstrs.contains(&"N") && bstrs.contains(&"H"));
        assert!(cstrs.contains(&"N") && cstrs.contains(&"H"));
        assert!(bstrs.iter().any(|t| bytes(t).contains(&0)));
        assert!(cstrs.iter().all(|t| !bytes(t).contains(&0)));
        assert!(bstrs.iter().any(|t| bytes(t).iter().any(|b| *b >= 0x80)));
        for n in [15, 16, 17, 32, 64] {
            assert!(bstrs.iter().any(|t| bytes(t).len() == n), "length {n}");
        }
        assert!(cases.iter().any(|c| c[0] == c[1] && c[0].len() > 3));
    }

    #[test]
    fn integers_stay_in_range_and_hit_the_edges() {
        let d = Dictionary {
            strings: vec![],
            ints: vec![1000],
        };
        let ty = IntType {
            kind: IntKind::Int,
            bits: 32,
            signed: true,
        };
        let params = vec![(
            "n".to_owned(),
            Shape::Int {
                ty,
                c_type: "int".into(),
            },
        )];
        let mut g = Gen::new(3, "f", &d);
        let vals: Vec<i64> = (0..4000)
            .map(|_| g.case(&params).parse().unwrap())
            .collect();
        assert!(vals.iter().all(|v| i32::try_from(*v).is_ok()));
        for want in [
            0,
            -1,
            i64::from(i32::MAX),
            i64::from(i32::MIN),
            999,
            1000,
            1001,
        ] {
            assert!(vals.contains(&want), "{want}");
        }
    }
}
