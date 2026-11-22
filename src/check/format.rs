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

/// Which family of formats a function's arguments reach.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    /// `vsnprintf`: the arguments are values.
    Printf,
    /// `vsscanf`: the arguments are pointers to objects it stores into.
    Scanf,
}

impl Kind {
    pub(crate) const fn formats(self) -> &'static [&'static str] {
        match self {
            Self::Printf => PRINTF,
            Self::Scanf => SCANF,
        }
    }
}

/// The formats a `scanf`-like function is called with: the integer, text
/// and `%n` conversions the model covers, with widths, suppression, length
/// modifiers, white space and ordinary characters, and the shapes of the
/// formats mpv passes (`%u:%u%n`, `%x.%u`).
pub(crate) const SCANF: &[&str] = &[
    "%d",
    "%u",
    "%x",
    "%X",
    "%o",
    "%i",
    "%ld",
    "%lu",
    "%lld",
    "%llx",
    "%hd",
    "%hu",
    "%hhd",
    "%hhu",
    "%zu",
    "%jd",
    "%d%n",
    "%u:%u%n",
    "%u:%u:%u%n",
    "%x.%u",
    "%3d",
    "%2x%d",
    "%d %d",
    " %d",
    "%d,%d,%d",
    "abc%d",
    "%%%d",
    "%*d %d",
    "%c",
    "%d%c",
    "%7s",
    "%7s%n",
    "%3s%3s",
    "%n",
    "",
    "x%n",
    "%10d%n",
];

/// The object one `scanf` conversion stores into.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Target {
    /// The C type of the object, as `VaList.argPtr` compares it; `char`
    /// for the characters of `%c` and `%s`.
    pub(crate) pointee: &'static str,
    /// Bytes of the object.
    pub(crate) size: u64,
}

/// The objects `fmt` stores into, in order.
pub(crate) fn scanf_targets(fmt: &str) -> Vec<Target> {
    let b = fmt.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        if b.get(i) != Some(&b'%') {
            i += 1;
            continue;
        }
        i += 1;
        let skip = b.get(i) == Some(&b'*');
        if skip {
            i += 1;
        }
        let start = i;
        while b.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
        let width: Option<u64> = std::str::from_utf8(b.get(start..i).unwrap_or_default())
            .ok()
            .and_then(|w| w.parse().ok());
        let start = i;
        while b.get(i).is_some_and(|c| b"hlzjt".contains(c)) {
            i += 1;
        }
        let len = b.get(start..i).unwrap_or_default();
        let conv = b.get(i).copied();
        i += 1;
        let signed = matches!(conv, Some(b'd' | b'i' | b'n'));
        let int = |s: &'static str, u: &'static str, size: u64| Target {
            pointee: if signed { s } else { u },
            size,
        };
        let t = match (conv, len) {
            (Some(b'd' | b'i' | b'u' | b'o' | b'x' | b'X' | b'n'), b"") => {
                int("int", "unsigned int", 4)
            }
            (Some(b'd' | b'i' | b'u' | b'o' | b'x' | b'X' | b'n'), b"hh") => {
                int("signed char", "unsigned char", 1)
            }
            (Some(b'd' | b'i' | b'u' | b'o' | b'x' | b'X' | b'n'), b"h") => {
                int("short", "unsigned short", 2)
            }
            (Some(b'd' | b'i' | b'u' | b'o' | b'x' | b'X' | b'n'), b"l" | b"z" | b"j" | b"t") => {
                int("long", "unsigned long", 8)
            }
            (Some(b'd' | b'i' | b'u' | b'o' | b'x' | b'X' | b'n'), b"ll") => {
                int("long long", "unsigned long long", 8)
            }
            (Some(b'c'), _) => Target {
                pointee: "char",
                size: width.unwrap_or(1),
            },
            (Some(b's'), _) => Target {
                pointee: "char",
                size: width.map_or(64, |w| w + 1),
            },
            _ => continue,
        };
        if !skip {
            out.push(t);
        }
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
        let t = scanf_targets("%u:%*d%7s%hhd%n");
        let p: Vec<(&str, u64)> = t.iter().map(|t| (t.pointee, t.size)).collect();
        assert_eq!(
            p,
            [
                ("unsigned int", 4),
                ("char", 8),
                ("signed char", 1),
                ("int", 4)
            ]
        );
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
