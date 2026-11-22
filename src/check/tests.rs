//! `achates check` on `tests/fixtures/check.c`: a correct function agrees
//! and its planted bugs are caught, a deliberately wrong emitted definition
//! disagrees on a named input, an unsupported parameter type is reported
//! with its reason, and a function whose only mutant is equivalent is not
//! called sensitive.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use anyhow::{Context as _, Result};

use crate::check::{self, FnResult, Options, Report, Status};
use crate::compdb;

fn fixture_dir(tag: &str) -> Result<PathBuf> {
    let dir = std::env::temp_dir().join(format!("achates-check-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir)?;
    std::fs::write(
        dir.join("check.c"),
        include_str!("../../tests/fixtures/check.c"),
    )?;
    std::fs::write(
        dir.join("compile_commands.json"),
        format!(
            r#"[{{"directory": "{}", "file": "check.c", "command": "cc -std=c11 -O1 -c check.c"}}]"#,
            dir.display()
        ),
    )?;
    Ok(dir)
}

fn run(
    tag: &str,
    functions: &[&str],
    count: usize,
    tamper: Option<&check::Tamper>,
) -> Result<Report, String> {
    let go = || -> Result<Report> {
        let dir = fixture_dir(tag)?;
        let entries = compdb::load(&dir.join("compile_commands.json"))?;
        let picked = compdb::select(&entries, "check.c")?;
        let opts = Options {
            name: "Fix".into(),
            runtime: Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"),
            work: dir.join("work"),
            functions: functions.iter().map(|f| (*f).to_owned()).collect(),
            count,
            seed: 1,
            mutants: 24,
            jobs: 2,
            cflags_file: None,
            link_file: None,
        };
        let r = check::run(&picked, &opts, tamper);
        let _ = std::fs::remove_dir_all(&dir);
        r
    };
    go().map_err(|e| format!("{e:#}"))
}

fn honest() -> &'static Report {
    static RUN: OnceLock<Result<Report, String>> = OnceLock::new();
    let all = [
        "clamp_add",
        "twice",
        "count_a",
        "order",
        "same",
        "via_union",
        "half",
        "format_sum",
        "vformat_sum",
        "list_chars",
    ];
    match RUN.get_or_init(|| run("honest", &all, 400, None)) {
        Ok(r) => r,
        Err(e) => panic!("{e}"),
    }
}

fn result<'a>(r: &'a Report, name: &str) -> &'a FnResult {
    r.functions
        .iter()
        .find(|f| f.function == name)
        .unwrap_or_else(|| panic!("{name} missing from the report:\n{}", r.summary()))
}

#[test]
fn a_correct_function_agrees_and_catches_its_mutants() {
    let r = honest();
    for name in ["clamp_add", "twice", "count_a", "order"] {
        let f = result(r, name);
        assert_eq!(
            f.status,
            Status::CheckedSensitive,
            "{name}:\n{}",
            r.summary()
        );
        assert_eq!(f.disagreements, 0);
        assert!(f.compared > 0);
        let m = f.mutants.as_ref().expect("mutants were run");
        assert!(m.caught > 0 && m.caught <= m.compiled && m.compiled <= m.generated);
        assert_eq!(m.survivors.len(), m.compiled - m.caught);
    }
}

#[test]
fn printf_arguments_and_string_lists_are_checked() {
    let r = honest();
    for name in ["format_sum", "vformat_sum", "list_chars"] {
        let f = result(r, name);
        assert_eq!(
            f.status,
            Status::CheckedSensitive,
            "{name}:\n{}",
            r.summary()
        );
        assert_eq!(f.disagreements, 0);
        assert!(f.compared > f.inputs / 2, "{name}: {f:?}");
    }
}

#[test]
fn undefined_inputs_are_counted_and_not_compared() {
    let r = honest();
    // `x / 2 * 4` overflows for large `x`; a null `p` is dereferenced.
    for name in ["twice", "order"] {
        let f = result(r, name);
        assert!(f.undefined > 0, "{name}");
        assert_eq!(f.compared + f.undefined + f.aborts, f.inputs, "{name}");
    }
}

#[test]
fn a_failed_assertion_must_abort_the_compiled_c_too() {
    let f = result(honest(), "half");
    assert_eq!(f.status, Status::CheckedSensitive);
    assert!(f.aborts > 0 && f.compared > 0, "{f:?}");
}

#[test]
fn an_equivalent_mutant_is_not_evidence_of_sensitivity() {
    let f = result(honest(), "same");
    assert_eq!(f.status, Status::CheckedNotShownSensitive);
    let m = f.mutants.as_ref().expect("mutants were run");
    assert_eq!((m.generated, m.caught), (1, 0));
    assert_eq!(
        m.survivors.first().map(|s| s.before.as_str()),
        Some("y = x;")
    );
}

#[test]
fn an_unsupported_parameter_is_not_checkable_with_its_reason() {
    let f = result(honest(), "via_union");
    assert_eq!(f.status, Status::NotCheckable);
    assert_eq!(
        f.reasons,
        vec!["parameter type: union u: a union".to_owned()]
    );
    assert_eq!(f.inputs, 0);
}

#[test]
fn a_corrupted_definition_disagrees_on_a_reported_input() {
    let tamper = |dir: &Path| -> Result<()> {
        let path = dir.join("Fix/Check_c.lean");
        let text = std::fs::read_to_string(&path).context("reading the emitted fixture")?;
        let wrong = "SInt.mul t1 (5 : I32)";
        let fixed = text.replacen("SInt.mul t1 (4 : I32)", wrong, 1);
        anyhow::ensure!(
            fixed.contains(wrong),
            "the definition of `twice` changed shape"
        );
        std::fs::write(&path, fixed).context("writing the corrupted fixture")
    };
    let r = match run("tampered", &["twice"], 400, Some(&tamper)) {
        Ok(r) => r,
        Err(e) => panic!("{e}"),
    };
    let f = result(&r, "twice");
    assert_eq!(f.status, Status::Disagrees, "{}", r.summary());
    assert!(r.any_disagreement());
    let d = f.first.as_ref().expect("the first disagreement is kept");
    // The input is the one argument; the C result is twice the Lean one's
    // four-fifths, so the two lines differ in `ret` only.
    let x: i64 = d.input.parse().expect("one integer argument");
    let c_ret = x / 2 * 4;
    assert_eq!(d.c, format!("ok ret={c_ret}"));
    assert_eq!(d.lean, format!("ok ret={}", x / 2 * 5));
    assert!(
        f.mutants.is_none(),
        "no mutants are tried once the original disagrees"
    );
}

#[test]
fn many_calls_do_not_make_the_model_quadratic() {
    // Before `Mem.alloc` stopped copying the block array, the 90,000 calls
    // took about 14 s per input; now they take well under one.
    let r = match run("calls", &["many_calls"], 2, None) {
        Ok(r) => r,
        Err(e) => panic!("{e}"),
    };
    let f = result(&r, "many_calls");
    assert_eq!(f.compared, 2, "{}", r.summary());
    assert!(f.seconds < 10.0, "{} s", f.seconds);
}
