//! Format strings for functions that take `printf` arguments: the formats
//! the check passes, and the arguments each one asks for.
//!
//! A function whose `...` (or `va_list`) reaches `vsnprintf` is checked
//! with a format from [`PRINTF`] and arguments of the types that format
//! asks for, so that every call is defined C as far as the types go. The
//! values are generated as for any parameter of those types.

/// The C type of one argument a format asks for, after the default
/// argument promotions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Arg {
    Int,
    UInt,
    Long,
    ULong,
    LongLong,
    ULongLong,
    Double,
    /// A NUL-terminated string.
    Str,
    /// An `int` field width or precision given as `*`.
    Star,
}

impl Arg {
    pub(crate) const fn c_type(self) -> &'static str {
        match self {
            Self::Int | Self::Star => "int",
            Self::UInt => "unsigned int",
            Self::Long => "long",
            Self::ULong => "unsigned long",
            Self::LongLong => "long long",
            Self::ULongLong => "unsigned long long",
            Self::Double => "double",
            Self::Str => "char *",
        }
    }

    /// The width and signedness of an integer argument.
    pub(crate) const fn int(self) -> Option<(u32, bool)> {
        match self {
            Self::Int | Self::Star => Some((32, true)),
            Self::UInt => Some((32, false)),
            Self::Long | Self::LongLong => Some((64, true)),
            Self::ULong | Self::ULongLong => Some((64, false)),
            Self::Double | Self::Str => None,
        }
    }

    /// The rank `VArg` names an integer argument's type by.
    pub(crate) const fn rank(self) -> &'static str {
        match self {
            Self::Long | Self::ULong => "long",
            Self::LongLong | Self::ULongLong => "long long",
            _ => "int",
        }
    }
}

/// The formats a `printf`-like function is called with: every flag, field
/// width and precision form, every length modifier the model covers, and
/// the formats `misc/` itself passes.
pub(crate) const PRINTF: &[&str] = &[
    "%d",
    "%i",
    "%5d",
    "%-5d|",
    "%05d",
    "%+d",
    "% d",
    "%.3d",
    "%.0d",
    "%hhd",
    "%hd",
    "%ld",
    "%lld",
    "%u",
    "%lu",
    "%llu",
    "%zu",
    "%x",
    "%X",
    "%#x",
    "%08x",
    "%o",
    "%#o",
    "%02X",
    "\\u%04x",
    "%hhx",
    "%hx",
    "%c",
    "\\%c",
    "%3c|",
    "%s",
    "%.3s",
    "%8s|",
    "%-8s|",
    "%s%s",
    "%f",
    "%.2f",
    "%.0f",
    "%#.0f",
    "%10.3f",
    "%-+12.4f|",
    "%010.2f",
    "%F",
    "%.17f",
    "%s%f%s",
    "%*d",
    "%-*d|",
    "%.*d",
    "%*.*s|",
    "%%",
    "",
    "plain text",
    "a%db%sc%fd",
    "%d %u %x %c %s %f",
];

/// The arguments `fmt` asks for, in order.
pub(crate) fn printf_args(fmt: &str) -> Vec<Arg> {
    let b = fmt.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b.get(i) != Some(&b'%') {
            i += 1;
            continue;
        }
        i += 1;
        while b.get(i).is_some_and(|c| b"-+ #0".contains(c)) {
            i += 1;
        }
        if b.get(i) == Some(&b'*') {
            out.push(Arg::Star);
            i += 1;
        }
        while b.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
        if b.get(i) == Some(&b'.') {
            i += 1;
            if b.get(i) == Some(&b'*') {
                out.push(Arg::Star);
                i += 1;
            }
            while b.get(i).is_some_and(u8::is_ascii_digit) {
                i += 1;
            }
        }
        let start = i;
        while b.get(i).is_some_and(|c| b"hlzjt".contains(c)) {
            i += 1;
        }
        let len = b.get(start..i).unwrap_or_default();
        let conv = b.get(i).copied();
        i += 1;
        let signed = matches!(conv, Some(b'd' | b'i'));
        let arg = match (conv, len) {
            (Some(b'd' | b'i' | b'u' | b'o' | b'x' | b'X'), b"l" | b"z" | b"j" | b"t") => {
                if signed { Arg::Long } else { Arg::ULong }
            }
            (Some(b'd' | b'i' | b'u' | b'o' | b'x' | b'X'), b"ll") => {
                if signed {
                    Arg::LongLong
                } else {
                    Arg::ULongLong
                }
            }
            (Some(b'd' | b'i' | b'c'), _) => Arg::Int,
            (Some(b'u' | b'o' | b'x' | b'X'), _) => Arg::UInt,
            (Some(b's'), _) => Arg::Str,
            (Some(b'f' | b'F'), _) => Arg::Double,
            _ => continue,
        };
        out.push(arg);
    }
    out
}

/// A C string literal holding `s`.
pub(crate) fn c_literal(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_ask_for_their_arguments() {
        assert_eq!(printf_args("%d"), [Arg::Int]);
        assert_eq!(printf_args("%%"), []);
        assert_eq!(printf_args("%*.*s|"), [Arg::Star, Arg::Star, Arg::Str]);
        assert_eq!(
            printf_args("%zu %lld %hhx"),
            [Arg::ULong, Arg::LongLong, Arg::UInt]
        );
        assert_eq!(printf_args("a%db%sc%fd"), [Arg::Int, Arg::Str, Arg::Double]);
        assert_eq!(printf_args("\\%c"), [Arg::Int]);
        for f in PRINTF {
            let n = f.matches('%').count() - 2 * f.matches("%%").count();
            assert_eq!(
                printf_args(f).iter().filter(|a| **a != Arg::Star).count(),
                n,
                "{f}"
            );
        }
    }
}
