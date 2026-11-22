//! The templates: from the C and Rust signatures of a pair, the Lean
//! statement of their equality, or the reason no template applies.

use std::fmt::Write as _;

use crate::equiv::lean::Def;

/// How a C scalar becomes the Rust one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Conv {
    /// The same Lean type on both sides (`Bool`).
    Id,
    /// Through this function of `Equiv`.
    Fn(&'static str),
}

/// How one argument is passed on each side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Arg {
    /// An integer or `_Bool`.
    Scalar(Conv),
    /// A `struct bstr` by value; Rust takes the bytes as a slice.
    Bstr,
    /// A pointer to a NUL-terminated string; Rust takes the bytes before
    /// the NUL as a slice.
    CStr,
}

/// How the result corresponds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Res {
    /// `y = conv r`.
    Scalar(Conv),
    /// A C truth value (0 or 1) and a Rust `bool`.
    Truth,
    /// A `struct bstr` view and a Rust slice, compared by bytes.
    Bstr,
}

/// A pair the templates cover.
#[derive(Debug, Clone)]
pub(crate) struct Statement {
    pub(crate) shape: String,
    pub(crate) text: String,
    /// The hypotheses of the statement, each in words, for the report.
    pub(crate) preconditions: Vec<String>,
}

/// The C prototype as the front end reads it, for what the Lean types do
/// not say (which struct an `Agg` is, what a `Ptr` points to).
#[derive(Debug, Clone)]
pub(crate) struct Proto {
    pub(crate) params: Vec<String>,
    pub(crate) ret: String,
}

fn int_conv(c: &str, r: &str) -> Option<Conv> {
    Some(Conv::Fn(match (c, r) {
        ("U8", "Std.U8") => "Equiv.u8",
        ("U16", "Std.U16") => "Equiv.u16",
        ("U32", "Std.U32") => "Equiv.u32",
        ("U64", "Std.U64") => "Equiv.u64",
        ("I8", "Std.I8") => "Equiv.i8",
        ("I16", "Std.I16") => "Equiv.i16",
        ("I32", "Std.I32") => "Equiv.i32",
        ("I64", "Std.I64") => "Equiv.i64",
        ("I8", "Std.U8") => "Equiv.charU8",
        ("Bool", "Bool") => return Some(Conv::Id),
        _ => return None,
    }))
}

fn is_char_ptr(ir: &str) -> bool {
    ir.starts_with("ptr<") && (ir.contains("char:i8") || ir.contains("char:u8"))
}

fn arg(c_lean: &str, ir: &str, rust: &str) -> Result<Arg, String> {
    if let Some(conv) = int_conv(c_lean, rust) {
        return Ok(Arg::Scalar(conv));
    }
    match (c_lean, rust) {
        ("Agg", "Slice Std.U8") if ir == "struct bstr" => Ok(Arg::Bstr),
        ("Ptr", "Slice Std.U8") if is_char_ptr(ir) => Ok(Arg::CStr),
        _ => Err(format!("argument `{ir}` ↔ `{rust}`")),
    }
}

fn res(c_lean: &str, ir: &str, rust: &str) -> Result<Res, String> {
    if let Some(conv) = int_conv(c_lean, rust) {
        return Ok(Res::Scalar(conv));
    }
    match (c_lean, rust) {
        ("I32", "Bool") => Ok(Res::Truth),
        ("Agg", "Slice Std.U8") if ir == "struct bstr" => Ok(Res::Bstr),
        _ => Err(format!("result `{ir}` ↔ `{rust}`")),
    }
}

fn apply(conv: Conv, x: &str) -> String {
    match conv {
        Conv::Id => x.to_owned(),
        Conv::Fn(c) => format!("({c} {x})"),
    }
}

/// The C parameters a port drops: the talloc parent of what the function
/// allocates, and the logger.
const DROPPED: [&str; 3] = ["talloc_ctx", "ta_parent", "log"];

/// One C parameter: its Lean name and type, its C type, and how it passes.
struct Param<'a> {
    name: &'a str,
    lean: &'a str,
    ir: &'a str,
    arg: Arg,
}

/// The parameters and result of a pair, or why no template takes them.
fn signature<'a>(
    c: &'a Def,
    proto: &'a Proto,
    rust: &Def,
) -> Result<(Vec<Param<'a>>, Res), String> {
    let c_params: Vec<(&(String, String), &String)> = c
        .params
        .iter()
        .filter(|(n, _)| n != "fuel")
        .zip(&proto.params)
        .collect();
    if c_params
        .iter()
        .any(|((n, _), _)| DROPPED.contains(&n.as_str()))
    {
        return Err("allocation: the C side takes a talloc parent or a logger".to_owned());
    }
    if c_params.len() != rust.params.len() {
        return Err(format!(
            "parameter lists differ: C has {}, Rust has {}",
            c_params.len(),
            rust.params.len()
        ));
    }
    let mut params = Vec::new();
    for (((n, ct), ir), (_, rt)) in c_params.iter().zip(&rust.params) {
        params.push(Param {
            name: n,
            lean: ct,
            ir,
            arg: arg(ct, ir, rt)?,
        });
    }
    let c_ret = c.ret.strip_prefix("M ").unwrap_or(&c.ret);
    let r_ret = rust.ret.strip_prefix("Result ").unwrap_or(&rust.ret);
    let r_ret = r_ret
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(r_ret);
    if r_ret.contains('×') {
        return Err("output through a pointer: Rust returns a tuple".to_owned());
    }
    Ok((params, res(c_ret, &proto.ret, r_ret)?))
}

/// The statement for one pair, or why there is none.
///
/// `reads_statics` says that the C side reads objects with static storage,
/// so the memory must hold them as `Statics.init` leaves them.
pub(crate) fn statement(
    thm: &str,
    c: &Def,
    proto: &Proto,
    rust: &Def,
    reads_statics: bool,
    tactic: &str,
) -> Result<Statement, String> {
    let (params, result) = signature(c, proto, rust)?;
    let mut binders = String::from("(m : Achates.Mem)");
    let mut c_args = String::new();
    let mut r_args = String::new();
    let mut pre = Vec::new();
    let mut kinds = Vec::new();
    if reads_statics {
        binders.push_str(" (h_statics : Equiv.StaticsReady m)");
        pre.push("the memory holds the static objects as `Statics.init` leaves them".to_owned());
    }
    for p in &params {
        let (n, ir) = (p.name, p.ir);
        let _ = write!(c_args, " {n}");
        let (binder, kind) = match p.arg {
            Arg::Scalar(conv) => {
                let _ = write!(r_args, " {}", apply(conv, n));
                (format!("({n} : Achates.{})", p.lean), "scalar")
            }
            Arg::Bstr => {
                let _ = write!(r_args, " s_{n}");
                pre.push(format!(
                    "`{n}` (`{ir}`) is a view of `s_{n}`: its start is an object pointer to live memory holding those bytes"
                ));
                (
                    format!(
                        "({n} : Achates.Agg) (s_{n} : Aeneas.Std.Slice Aeneas.Std.U8) (h_{n} : Equiv.IsBstr m {n} s_{n})"
                    ),
                    "bstr",
                )
            }
            Arg::CStr => {
                let _ = write!(r_args, " s_{n}");
                pre.push(format!(
                    "`{n}` (`{ir}`) points to live memory holding the bytes of `s_{n}` and then a NUL"
                ));
                (
                    format!(
                        "({n} : Achates.Ptr) (s_{n} : Aeneas.Std.Slice Aeneas.Std.U8) (h_{n} : Equiv.IsCStr m {n} s_{n})"
                    ),
                    "C string",
                )
            }
        };
        let _ = write!(binders, " {binder}");
        kinds.push(kind);
    }
    let (rel, res_kind) = match result {
        Res::Scalar(conv) => (format!("y = {}", apply(conv, "r")), "scalar"),
        Res::Truth => ("r = Equiv.ofBool y".to_owned(), "truth value"),
        Res::Bstr => ("Equiv.IsBstr m' r y".to_owned(), "bstr view"),
    };
    kinds.sort_unstable();
    kinds.dedup();
    let arg_kinds = if kinds.is_empty() {
        "no".to_owned()
    } else {
        kinds.join(" and ")
    };
    let shape = format!("{arg_kinds} arguments, {res_kind} result");
    let text = format!(
        "/-- `{}` and `{}`. Shape: {shape}. -/\ntheorem {thm} {binders} :\n    \
         Equiv.Equal (fun r m' y => Equiv.Unchanged m m' ∧ {rel})\n      \
         (fun fuel => {} fuel{c_args}) m\n      ({}{r_args}) := by\n  {tactic}\n",
        c.name, rust.name, c.name, rust.name
    );
    Ok(Statement {
        shape,
        text,
        preconditions: pre,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn def(name: &str, params: &[(&str, &str)], ret: &str) -> Def {
        Def {
            name: name.to_owned(),
            params: params
                .iter()
                .map(|(a, b)| ((*a).to_owned(), (*b).to_owned()))
                .collect(),
            ret: ret.to_owned(),
            body: String::new(),
            axiom: false,
        }
    }

    #[test]
    fn bstr_arguments_and_an_int_result() {
        let c = def(
            "C.bstrcmp",
            &[("fuel", "Nat"), ("a", "Agg"), ("b", "Agg")],
            "M I32",
        );
        let r = def(
            "R.bstrcmp",
            &[("a", "Slice Std.U8"), ("b", "Slice Std.U8")],
            "Result Std.I32",
        );
        let p = Proto {
            params: vec!["struct bstr".into(), "struct bstr".into()],
            ret: "int:i32".into(),
        };
        let s = statement("t", &c, &p, &r, false, "tac").unwrap();
        assert_eq!(s.shape, "bstr arguments, scalar result");
        assert!(s.text.contains("(h_a : Equiv.IsBstr m a s_a)"));
        assert!(s.text.contains("y = (Equiv.i32 r)"));
        assert!(s.text.contains("(R.bstrcmp s_a s_b)"));
        assert_eq!(s.preconditions.len(), 2);
    }

    #[test]
    fn a_tuple_result_has_no_template() {
        let c = def("C.f", &[("fuel", "Nat"), ("a", "Agg")], "M I32");
        let r = def(
            "R.f",
            &[("a", "Slice Std.U8")],
            "Result (Std.I32 × (Slice Std.U8))",
        );
        let p = Proto {
            params: vec!["struct bstr".into()],
            ret: "int:i32".into(),
        };
        let e = statement("t", &c, &p, &r, false, "tac").unwrap_err();
        assert!(e.starts_with("output through a pointer"));
    }
}
