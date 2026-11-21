//! Fidelity tests: every `t_*` function of `tests/fixtures/fidelity.c` is
//! run as compiled C and as emitted Lean, and the results are compared.
//! One emission and one Lake build serve all cases.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use crate::compdb;
use crate::emit::{self, Options};

#[derive(Debug, Clone, Copy)]
enum Expect {
    /// The Lean result is `ok` with the value the compiled C returns.
    SameAsC,
    /// C gives the execution no meaning; Lean reports undefined behaviour
    /// with a reason containing this text.
    Ub(&'static str),
    /// Lean stops with a result starting with this text.
    Stops(&'static str),
}

struct Outcome {
    c: BTreeMap<String, String>,
    lean: BTreeMap<String, String>,
}

fn sh(cmd: &mut Command, what: &str) -> Result<String, String> {
    let lean_bin = std::env::var("HOME")
        .map(|h| format!("{h}/.local/lean/bin"))
        .unwrap_or_default();
    let path = format!("{lean_bin}:{}", std::env::var("PATH").unwrap_or_default());
    let out = cmd
        .env("PATH", path)
        .output()
        .map_err(|e| format!("{what}: {e}"))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(format!(
            "{what} failed:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ))
    }
}

fn parse(text: &str) -> BTreeMap<String, String> {
    text.lines()
        .filter_map(|l| l.split_once(' '))
        .map(|(a, b)| (a.to_owned(), b.to_owned()))
        .collect()
}

/// Emits `source` as a project named `Fix` under a fresh directory and
/// returns the directory and the summary.
fn emit_fixture(tag: &str, source: &str) -> Result<(PathBuf, String), String> {
    let dir = std::env::temp_dir().join(format!("achates-emit-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    std::fs::write(dir.join("fidelity.c"), source).map_err(|e| e.to_string())?;
    let db = dir.join("compile_commands.json");
    let entry = format!(
        r#"[{{"directory": "{}", "file": "fidelity.c", "command": "cc -std=c11 -O1 -c fidelity.c"}}]"#,
        dir.display()
    );
    std::fs::write(&db, entry).map_err(|e| e.to_string())?;
    let entries = compdb::load(&db).map_err(|e| format!("{e:#}"))?;
    let picked = compdb::select(&entries, "fidelity.c").map_err(|e| format!("{e:#}"))?;
    let opts = Options {
        out: dir.join("lean"),
        name: "Fix".into(),
        runtime: Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"),
    };
    let summary = emit::run(&picked, &opts).map_err(|e| format!("{e:#}"))?;
    Ok((dir, summary))
}

const RENDER: &str = r#"import Fix
open Achates
def render (r : Except Err I64) : String :=
  match r with
  | .ok v => s!"ok {v}"
  | .error (.ub m) => s!"ub {m}"
  | .error (.assertFail e _ _ _) => s!"assert {e}"
  | .error .abort => "abort"
  | .error (.unsupported m) => s!"unsupported {m}"
  | .error .outOfFuel => "fuel"
def main : IO Unit := do
"#;

fn run_all() -> Result<Outcome, String> {
    let source = include_str!("../../tests/fixtures/fidelity.c");
    let (dir, summary) = emit_fixture("fidelity", source)?;
    let mut lean = BTreeMap::new();
    let mut runner = RENDER.to_owned();
    for (name, _) in CASES {
        if summary.contains(&format!(" {name}: emitted")) {
            let _ = writeln!(
                runner,
                "  IO.println s!\"{name} {{render (do Fix.Statics.init; Fix.Fidelity_c.{name} 10000 : M I64).eval}}\""
            );
        } else {
            let why = summary
                .lines()
                .find(|l| l.contains(&format!(" {name}: ")))
                .unwrap_or("absent from the summary");
            lean.insert((*name).to_owned(), format!("refused {why}"));
        }
    }
    let project = dir.join("lean");
    std::fs::write(project.join("Run.lean"), runner).map_err(|e| e.to_string())?;
    sh(
        Command::new("lake")
            .args(["build", "--wfail"])
            .current_dir(&project),
        "lake build of the emitted fixture",
    )?;
    let out = sh(
        Command::new("lake")
            .args(["env", "lean", "--run", "Run.lean"])
            .current_dir(&project),
        "running the emitted fixture",
    )?;
    lean.extend(parse(&out));

    let mut main = String::from("#include <stdio.h>\n#include \"fidelity.c\"\nint main(void) {\n");
    for (name, _) in CASES.iter().filter(|c| matches!(c.1, Expect::SameAsC)) {
        let _ = writeln!(main, "    printf(\"{name} ok %lld\\n\", {name}());");
    }
    main.push_str("    return 0;\n}\n");
    std::fs::write(dir.join("main.c"), main).map_err(|e| e.to_string())?;
    sh(
        Command::new("cc")
            .args(["-std=c11", "-O1", "-o", "prog", "main.c"])
            .current_dir(&dir),
        "compiling the fixture",
    )?;
    let c = parse(&sh(
        &mut Command::new(dir.join("prog")),
        "running the compiled fixture",
    )?);
    let _ = std::fs::remove_dir_all(&dir);
    Ok(Outcome { c, lean })
}

fn check(name: &str) {
    static RUN: OnceLock<Result<Outcome, String>> = OnceLock::new();
    let outcome = match RUN.get_or_init(run_all) {
        Ok(o) => o,
        Err(e) => panic!("{e}"),
    };
    let expect = CASES.iter().find(|c| c.0 == name).expect("case listed").1;
    let lean = outcome.lean.get(name).map_or("no result", String::as_str);
    match expect {
        Expect::SameAsC => {
            let c = outcome.c.get(name).map_or("no result", String::as_str);
            assert_eq!(
                lean, c,
                "{name}: Lean (left) and compiled C (right) disagree"
            );
        }
        Expect::Ub(text) => {
            assert!(
                lean.starts_with("ub ") && lean.contains(text),
                "{name}: expected undefined behaviour mentioning `{text}`, got `{lean}`"
            );
        }
        Expect::Stops(text) => assert!(
            lean.starts_with(text),
            "{name}: expected `{text}`, got `{lean}`"
        ),
    }
}

macro_rules! cases {
    ($($name:ident => $expect:expr,)*) => {
        const CASES: &[(&str, Expect)] = &[$((stringify!($name), $expect),)*];
        $(#[test] fn $name() { check(stringify!($name)); })*
    };
}

use Expect::{SameAsC, Stops, Ub};

cases! {
    t_char_promotion => SameAsC,
    t_wrap_u8 => SameAsC,
    t_wrap_u16 => SameAsC,
    t_wrap_u32 => SameAsC,
    t_wrap_u64 => SameAsC,
    t_u16_mul_small => SameAsC,
    t_u16_mul_overflows_int => Ub("signed overflow in multiplication"),
    t_char_inc => SameAsC,
    t_uchar_compound => SameAsC,
    t_plain_char_is_signed => SameAsC,
    t_negate_unsigned => SameAsC,
    t_bitops => SameAsC,
    t_signed_overflow => Ub("signed overflow in addition"),
    t_div_truncates => SameAsC,
    t_div_zero => Ub("division by zero"),
    t_int_min_div => Ub("signed overflow in division"),
    t_int_min_rem => Ub("MIN % -1"),
    t_negate_int_min => Ub("signed overflow in negation"),
    t_cmp_signed_unsigned => SameAsC,
    t_cmp_long_unsigned => SameAsC,
    t_shift_31 => SameAsC,
    t_shift_32 => Ub("shift by 32"),
    t_shift_negative_count => Ub("shift by -1"),
    t_shift_into_sign => Ub("signed overflow in left shift"),
    t_shift_right_negative => SameAsC,
    t_shift_count_is_long => SameAsC,
    t_short_circuit => SameAsC,
    t_conditional_side_effects => SameAsC,
    t_comma => SameAsC,
    t_for_break_continue => SameAsC,
    t_do_while_continue => SameAsC,
    t_nested_loops => SameAsC,
    t_infinite_loop => Stops("fuel"),
    t_switch => SameAsC,
    t_switch_in_loop => SameAsC,
    t_goto_cleanup => SameAsC,
    t_struct_through_pointer => SameAsC,
    t_struct_by_value => SameAsC,
    t_compound_literal => SameAsC,
    t_union => SameAsC,
    t_enum => SameAsC,
    t_array_sum => SameAsC,
    t_2d_array => SameAsC,
    t_pointer_difference => SameAsC,
    t_out_parameter => SameAsC,
    t_string_walk => SameAsC,
    t_reinterpret_bytes => SameAsC,
    t_reinterpret_struct => SameAsC,
    t_read_past_array => Ub("access of 4 bytes at offset 12 of an object of 12 bytes"),
    t_pointer_past_array => Ub("pointer arithmetic leaves the object"),
    t_uninitialised_local => Ub("uninitialised"),
    t_use_after_free => Ub("after its lifetime ended"),
    t_double_free => Ub("already freed"),
    t_null_dereference => Ub("null pointer"),
    t_write_string_literal => Ub("string literal"),
    t_recursion => SameAsC,
    t_mutual_recursion => SameAsC,
    t_function_pointer => SameAsC,
    t_function_pointer_table => SameAsC,
    t_null_function_pointer => Ub("call through a null pointer"),
    t_global_updated => SameAsC,
    t_global_table => SameAsC,
    t_static_local => SameAsC,
    t_global_string_pointers => SameAsC,
    t_memcpy => SameAsC,
    t_memmove_overlapping => SameAsC,
    t_memcpy_overlapping => Ub("memcpy between overlapping objects"),
    t_compare_functions => SameAsC,
    t_search_functions => SameAsC,
    t_memset => SameAsC,
    t_assert_fails => Stops("assert x == 2"),
    t_abort => Stops("abort"),
    t_float_to_int => SameAsC,
    t_float_to_int_out_of_range => Ub("does not fit"),
    t_int_to_float => SameAsC,
    t_u64_to_double => SameAsC,
    t_double_arithmetic => SameAsC,
    t_single_precision => SameAsC,
    t_float_compare => SameAsC,
    t_nested_members => SameAsC,
    t_bool => SameAsC,
    t_pointer_compound => SameAsC,
    t_char_literals => SameAsC,
    t_global_struct => SameAsC,
    t_unsigned_division => SameAsC,
    t_long_overflow => Ub("signed overflow in addition"),
    t_integer_pointer_round_trip => SameAsC,
    t_do_while_zero => SameAsC,
    t_conditional_pointer => SameAsC,
    t_sizeof => SameAsC,
    t_uninitialised_char => Stops("unsupported read of an uninitialised byte"),
    t_partly_initialised_struct_copy => SameAsC,
    t_misaligned_access => Ub("needs alignment 4"),
    t_address_as_integer => Stops("unsupported conversion of an object or function address"),
}

fn refusal_of(tag: &str, source: &str, function: &str) -> String {
    let (dir, summary) = emit_fixture(tag, source).expect("emission runs");
    let _ = std::fs::remove_dir_all(dir);
    summary
        .lines()
        .find(|l| l.contains(&format!(" {function}: ")))
        .unwrap_or("")
        .to_owned()
}

#[test]
fn refuses_reading_variadic_arguments() {
    let src = "#include <stdarg.h>\nint f(int n, ...) { va_list ap; va_start(ap, n); va_end(ap); return n; }\n";
    let line = refusal_of("variadic", src, "f");
    assert!(
        line.contains("not emitted") && line.contains("variadic"),
        "{line}"
    );
}

#[test]
fn refuses_operands_whose_order_matters() {
    let src = "static int g; static int bump(void) { return ++g; }\nint f(void) { return bump() - bump(); }\nint h(int i) { return i + i++; }\n";
    let f = refusal_of("order", src, "f");
    assert!(f.contains("not emitted") && f.contains("sequence"), "{f}");
    let h = refusal_of("order2", src, "h");
    assert!(h.contains("not emitted") && h.contains("sequence"), "{h}");
}

#[test]
fn refuses_backward_goto() {
    let src = "int f(int n) { int i = 0; again: i++; if (i < n) goto again; return i; }\n";
    let line = refusal_of("goto", src, "f");
    assert!(
        line.contains("not emitted") && line.contains("goto"),
        "{line}"
    );
}

#[test]
fn unemitted_callee_becomes_a_parameter() {
    let src = "#include <stdarg.h>\nint v(int n, ...) { va_list ap; va_start(ap, n); va_end(ap); return n; }\nint f(void) { return v(1, 2); }\nint puts(const char *);\nint g(void) { return puts(\"x\"); }\n";
    let (dir, summary) = emit_fixture("param", src).expect("emission runs");
    let externals =
        std::fs::read_to_string(dir.join("lean/Fix/Externals.lean")).expect("externals written");
    let module =
        std::fs::read_to_string(dir.join("lean/Fix/Fidelity_c.lean")).expect("module written");
    let _ = std::fs::remove_dir_all(dir);
    assert!(
        summary.contains(" f: emitted") && summary.contains(" g: emitted"),
        "{summary}"
    );
    assert!(
        externals.contains("class Ext.puts where\n  call : Ptr → M I32"),
        "{externals}"
    );
    assert!(
        externals.contains("class Ext.v where\n  call : I32 → List VArg → M I32"),
        "{externals}"
    );
    assert!(
        module.contains("def g [Ext.puts] (fuel : Nat) : M I32"),
        "{module}"
    );
}
