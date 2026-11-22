//! When a line the Lean driver printed and a line the C harness printed
//! count as the same result.

/// How the Lean definition ended on one input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Class {
    Ok,
    /// Undefined behaviour: the C standard says nothing, so C is not run.
    Undefined,
    /// A failed `assert` or a call of `abort`: C must die from `abort` too.
    Aborts,
    /// Defined C the model does not cover: nothing to compare.
    Unsupported,
    OutOfFuel,
    /// The driver itself failed, or printed something else.
    Broken,
}

pub(crate) fn class(lean: &str) -> Class {
    let head = lean.split(' ').next().unwrap_or("");
    match head {
        "ok" => Class::Ok,
        "ub" => Class::Undefined,
        "assert" | "abort" => Class::Aborts,
        "unsupported" => Class::Unsupported,
        "fuel" => Class::OutOfFuel,
        _ => Class::Broken,
    }
}

fn is_word(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '?' | ':' | '+' | '_' | '-')
}

/// Splits a result into words and single separator characters.
fn words(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut start = None;
    for (i, c) in s.char_indices() {
        if is_word(c) {
            start.get_or_insert(i);
        } else {
            if let Some(b) = start.take() {
                out.push(s.get(b..i).unwrap_or(""));
            }
            out.push(s.get(i..i + c.len_utf8()).unwrap_or(""));
        }
    }
    if let Some(b) = start {
        out.push(s.get(b..).unwrap_or(""));
    }
    out
}

/// The bits of a float the drivers printed as `D<bits>` or `S<bits>`, with
/// the width of the exponent and of the fraction.
fn float_bits(w: &str) -> Option<(u64, u32, u32)> {
    let (tag, digits) = (w.get(..1)?, w.get(1..)?);
    let (exp, frac) = match tag {
        "D" => (11, 52),
        "S" => (8, 23),
        _ => return None,
    };
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some((digits.parse().ok()?, exp, frac))
}

/// Bit patterns must be equal, with two exceptions: any NaN equals any NaN
/// (C does not fix the payload or the sign of a NaN result), and a zero
/// equals a zero of the other sign (the build passes `-fno-signed-zeros`,
/// which lets the compiler pick either).
fn floats_agree(a: (u64, u32, u32), b: (u64, u32, u32)) -> bool {
    if a == b {
        return true;
    }
    if (a.1, a.2) != (b.1, b.2) {
        return false;
    }
    let (exp, frac) = (a.1, a.2);
    let magnitude = |x: u64| x & ((1u64 << (exp + frac)) - 1);
    let is_nan = |x: u64| {
        magnitude(x) >> frac == (1u64 << exp) - 1 && magnitude(x) & ((1u64 << frac) - 1) != 0
    };
    (is_nan(a.0) && is_nan(b.0)) || (magnitude(a.0) == 0 && magnitude(b.0) == 0)
}

/// Hexadecimal bytes agree when they are equal, where `??` in the Lean
/// text (a byte the model holds as indeterminate) agrees with any byte.
fn hex_agree(lean: &str, c: &str) -> bool {
    lean.contains("??")
        && lean.len() == c.len()
        && lean.len().is_multiple_of(2)
        && lean
            .as_bytes()
            .chunks(2)
            .zip(c.as_bytes().chunks(2))
            .all(|(l, r)| l == b"??" || l == r)
}

fn word_agrees(lean: &str, c: &str) -> bool {
    if lean == c {
        return true;
    }
    match (float_bits(lean), float_bits(c)) {
        (Some(a), Some(b)) => floats_agree(a, b),
        _ => hex_agree(lean, c),
    }
}

/// Whether a C result is the harness's report of a call that ran past its
/// time limit.
pub(crate) fn is_timeout(c: &str) -> bool {
    c.starts_with("timeout")
}

/// Whether the C harness's line reports what the Lean driver's line does.
pub(crate) fn agree(lean: &str, c: &str) -> bool {
    match class(lean) {
        Class::Aborts => c == "aborted",
        Class::Ok => {
            let (l, r) = (words(lean), words(c));
            l.len() == r.len() && l.iter().zip(&r).all(|(a, b)| word_agrees(a, b))
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_lines_agree_and_different_ones_do_not() {
        assert!(agree("ok ret=5 in0=6162", "ok ret=5 in0=6162"));
        assert!(!agree("ok ret=5 in0=6162", "ok ret=6 in0=6162"));
        assert!(!agree("ok ret=5", "ok ret=5 in0=61"));
    }

    #[test]
    fn floats_compare_by_bits_except_nan_payload_and_zero_sign() {
        let (pz, nz) = (0f64.to_bits(), (-0f64).to_bits());
        let (nan1, nan2) = (f64::NAN.to_bits(), f64::NAN.to_bits() | 1 | (1 << 63));
        assert!(agree(&format!("ok ret=D{pz}"), &format!("ok ret=D{nz}")));
        assert!(agree(
            &format!("ok ret=D{nan1}"),
            &format!("ok ret=D{nan2}")
        ));
        let one = 1f64.to_bits();
        assert!(!agree(
            &format!("ok ret=D{one}"),
            &format!("ok ret=D{}", one + 1)
        ));
        assert!(!agree(
            &format!("ok ret=D{}", f64::INFINITY.to_bits()),
            &format!("ok ret=D{nan1}")
        ));
        let (spz, snz) = (0f32.to_bits(), (-0f32).to_bits());
        assert!(agree(&format!("ok ret=S{spz}"), &format!("ok ret=S{snz}")));
        assert!(!agree(&format!("ok ret=S{spz}"), &format!("ok ret=D{pz}")));
    }

    #[test]
    fn an_indeterminate_byte_agrees_with_any_byte_and_only_there() {
        assert!(agree("ok ret=bstr(new,2,61??)", "ok ret=bstr(new,2,61ff)"));
        assert!(!agree("ok ret=bstr(new,2,61??)", "ok ret=bstr(new,2,62ff)"));
        assert!(!agree("ok ret=bstr(new,2,61??)", "ok ret=bstr(new,2,61)"));
    }

    #[test]
    fn a_model_abort_agrees_only_with_a_c_abort() {
        assert_eq!(class("assert x > 0"), Class::Aborts);
        assert!(agree("assert x > 0", "aborted"));
        assert!(agree("abort", "aborted"));
        assert!(!agree("assert x > 0", "returned"));
        assert!(!agree("abort", "signal 11"));
    }

    #[test]
    fn other_classes_never_agree() {
        assert_eq!(class("ub shift by 64"), Class::Undefined);
        assert_eq!(class("unsupported x"), Class::Unsupported);
        assert_eq!(class("fuel"), Class::OutOfFuel);
        assert_eq!(class("harness unsupported check harness: x"), Class::Broken);
        assert!(!agree("fuel", "fuel"));
    }
}
