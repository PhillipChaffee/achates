//! Where the C compilers are. `clang` reads the C; `cc` compiles the test
//! harnesses. Each is resolved once to an absolute path and tried on a
//! small program, because a directory early on `PATH` may hold a compiler
//! that cannot see the system headers (Lean's toolchain ships such a
//! `clang`), and using it fails far from the cause.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;

use anyhow::{Result, anyhow};

/// A compiler Achates needs, how to override the search, and how to tell
/// whether a candidate can be used.
struct Tool {
    name: &'static str,
    env: &'static str,
    /// Arguments that make the compiler read a C program from stdin.
    probe_args: &'static [&'static str],
    fallbacks: &'static [&'static str],
}

const PROBE: &str =
    "#include <stdlib.h>\n#include <stdio.h>\n#include <pthread.h>\nint main(void) { return 0; }\n";

const CLANG: Tool = Tool {
    name: "clang",
    env: "ACHATES_CLANG",
    probe_args: &["-fsyntax-only", "-x", "c", "-"],
    fallbacks: &["/usr/bin/clang", "/usr/local/bin/clang"],
};

const CC: Tool = Tool {
    name: "cc",
    env: "ACHATES_CC",
    probe_args: &["-x", "c", "-", "-o", "/dev/null"],
    fallbacks: &["/usr/bin/cc", "/usr/bin/gcc", "/usr/local/bin/cc"],
};

/// `Ok` when `path` compiles the probe program, else why it does not.
fn suitable(tool: &Tool, path: &Path) -> Result<(), String> {
    use std::io::Write as _;
    let mut child = Command::new(path)
        .args(tool.probe_args)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot be started: {e}"))?;
    if let Some(mut stdin) = child.stdin.take() {
        // A compiler that exits early closes the pipe; its status says why.
        let _ = stdin.write_all(PROBE.as_bytes());
    }
    let out = child
        .wait_with_output()
        .map_err(|e| format!("did not finish: {e}"))?;
    if out.status.success() {
        return Ok(());
    }
    let err = String::from_utf8_lossy(&out.stderr);
    let first = err
        .lines()
        .find(|l| l.contains("error"))
        .or_else(|| err.lines().next())
        .unwrap_or("no diagnostic");
    Err(format!(
        "cannot compile a program that includes <stdlib.h>, <stdio.h> and <pthread.h>: {}",
        first.trim()
    ))
}

fn candidates(tool: &Tool, path_var: &str) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::env::split_paths(path_var)
        .filter(|d| !d.as_os_str().is_empty())
        .map(|d| d.join(tool.name))
        .filter(|p| p.is_file())
        .collect();
    out.extend(
        tool.fallbacks
            .iter()
            .map(PathBuf::from)
            .filter(|p| p.is_file()),
    );
    let mut seen = Vec::new();
    out.retain(|p| {
        let real = std::fs::canonicalize(p).unwrap_or_else(|_| p.clone());
        if seen.contains(&real) {
            false
        } else {
            seen.push(real);
            true
        }
    });
    out
}

fn resolve(tool: &Tool, over: Option<&str>, path_var: &str) -> Result<PathBuf, String> {
    if let Some(given) = over.filter(|g| !g.is_empty()) {
        let p = PathBuf::from(given);
        return match suitable(tool, &p) {
            Ok(()) => Ok(p),
            Err(why) => Err(format!(
                "{}={given} is not a usable {}: it {why}",
                tool.env, tool.name
            )),
        };
    }
    let mut tried = Vec::new();
    for c in candidates(tool, path_var) {
        match suitable(tool, &c) {
            Ok(()) => return Ok(c),
            Err(why) => tried.push(format!("  {}: {why}", c.display())),
        }
    }
    Err(if tried.is_empty() {
        format!(
            "no `{}` found on PATH or in the usual places; set {} to the compiler to use",
            tool.name, tool.env
        )
    } else {
        format!(
            "no usable `{}`; set {} to the compiler to use. Tried:\n{}",
            tool.name,
            tool.env,
            tried.join("\n")
        )
    })
}

fn cached(cell: &'static OnceLock<Result<PathBuf, String>>, tool: &Tool) -> Result<&'static Path> {
    cell.get_or_init(|| {
        resolve(
            tool,
            std::env::var(tool.env).ok().as_deref(),
            &std::env::var("PATH").unwrap_or_default(),
        )
    })
    .as_deref()
    .map_err(|e| anyhow!("{e}"))
}

/// The clang that reads C for the front end.
pub(crate) fn clang() -> Result<&'static Path> {
    static CELL: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    cached(&CELL, &CLANG)
}

/// The system C compiler that builds test harnesses.
pub(crate) fn cc() -> Result<&'static Path> {
    static CELL: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    cached(&CELL, &CC)
}

/// Lean's `bin` directory, if Lean is unpacked in the usual place. Callers
/// append it to `PATH` for `lake`, after the system directories.
pub(crate) fn path_with_lean() -> String {
    let lean = std::env::var("HOME")
        .map(|h| format!("{h}/.local/lean/bin"))
        .unwrap_or_default();
    format!("{}:{lean}", std::env::var("PATH").unwrap_or_default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt as _;

    fn fake_dir(tag: &str, script: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("achates-tools-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        for name in ["clang", "cc"] {
            let p = dir.join(name);
            std::fs::write(&p, script).unwrap();
            std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        dir
    }

    const BROKEN: &str = "#!/bin/sh\ncat >/dev/null\necho \"x.c:1:10: fatal error: 'stdlib.h' file not found\" >&2\nexit 1\n";

    #[test]
    fn skips_a_compiler_without_system_headers_early_on_path() {
        let dir = fake_dir("skip", BROKEN);
        let path = format!(
            "{}:{}",
            dir.display(),
            std::env::var("PATH").unwrap_or_default()
        );
        for tool in [&CLANG, &CC] {
            let found = resolve(tool, None, &path).unwrap();
            assert!(!found.starts_with(&dir), "{} chosen", found.display());
        }
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn an_unusable_override_is_an_error_that_names_it() {
        let dir = fake_dir("override", BROKEN);
        let given = dir.join("clang");
        let err = resolve(&CLANG, Some(&given.to_string_lossy()), "").unwrap_err();
        assert!(
            err.contains("ACHATES_CLANG=") && err.contains("stdlib.h"),
            "{err}"
        );
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn no_usable_compiler_lists_what_was_tried() {
        let dir = fake_dir("none", BROKEN);
        let only = Tool {
            fallbacks: &[],
            ..CLANG
        };
        let err = resolve(&only, None, &dir.to_string_lossy()).unwrap_err();
        assert!(
            err.contains("no usable `clang`")
                && err.contains("ACHATES_CLANG")
                && err.contains(&*dir.join("clang").to_string_lossy()),
            "{err}"
        );
        let _ = std::fs::remove_dir_all(dir);
    }
}
