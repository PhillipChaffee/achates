//! Reading `compile_commands.json`, choosing entries, and turning a gcc
//! command line into one clang accepts.

use std::collections::HashSet;
use std::path::{Component, Path, PathBuf};

use anyhow::{Context as _, Result, bail};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct RawEntry {
    directory: String,
    file: String,
    command: Option<String>,
    arguments: Option<Vec<String>>,
}

/// One translation unit from the compilation database.
#[derive(Debug, Clone)]
pub(crate) struct Entry {
    pub(crate) directory: PathBuf,
    /// The file as the database spells it; clang echoes this spelling back.
    pub(crate) file: String,
    /// Absolute, lexically normalized path of the file.
    pub(crate) path: PathBuf,
    /// Full argument vector, compiler included.
    pub(crate) argv: Vec<String>,
}

pub(crate) fn load(path: &Path) -> Result<Vec<Entry>> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("reading compilation database {}", path.display()))?;
    let raw: Vec<RawEntry> = serde_json::from_str(&text)
        .with_context(|| format!("parsing compilation database {}", path.display()))?;
    let db_dir = path.parent().unwrap_or_else(|| Path::new("."));
    let mut seen = HashSet::new();
    let mut entries = Vec::new();
    for r in raw {
        let directory = normalize(&db_dir.join(&r.directory));
        let file_path = normalize(&directory.join(&r.file));
        let argv = match (r.arguments, r.command) {
            (Some(a), _) => a,
            (None, Some(c)) => {
                shell_split(&c).with_context(|| format!("splitting the command for {}", r.file))?
            }
            (None, None) => bail!("entry for {} has neither `arguments` nor `command`", r.file),
        };
        // A file compiled twice would be surveyed twice; the first command wins.
        if seen.insert(file_path.clone()) {
            entries.push(Entry {
                directory,
                file: r.file,
                path: file_path,
                argv,
            });
        }
    }
    Ok(entries)
}

/// Lexical normalization: no symlink resolution, so paths stay comparable
/// with the spellings clang prints.
pub(crate) fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                if !out.pop() {
                    out.push("..");
                }
            }
            other => out.push(other.as_os_str()),
        }
    }
    out
}

/// A selector is a path prefix, or a glob when it contains `*` or `?`. It
/// matches when the file's absolute path, or any trailing run of its
/// components, matches; so `misc/` selects `/x/.mpv/misc/bstr.c`.
pub(crate) fn select<'a>(entries: &'a [Entry], selector: &str) -> Result<Vec<&'a Entry>> {
    let is_glob = selector.contains(['*', '?']);
    let picked: Vec<&Entry> = entries
        .iter()
        .filter(|e| {
            suffixes(&e.path).iter().any(|s| {
                if is_glob {
                    glob_match(selector, s)
                } else {
                    s.starts_with(selector)
                }
            })
        })
        .collect();
    if picked.is_empty() {
        bail!("selector `{selector}` matches no file in the compilation database");
    }
    Ok(picked)
}

fn suffixes(p: &Path) -> Vec<String> {
    let full = p.to_string_lossy().into_owned();
    let mut out = vec![full.clone()];
    let mut rest = full.as_str();
    while let Some(i) = rest.find('/') {
        rest = rest.get(i + 1..).unwrap_or("");
        if !rest.is_empty() {
            out.push(rest.to_owned());
        }
    }
    out
}

/// `*` matches within one path component, `**` across components, `?` one
/// character other than `/`.
pub(crate) fn glob_match(pattern: &str, text: &str) -> bool {
    let p: Vec<char> = pattern.chars().collect();
    let t: Vec<char> = text.chars().collect();
    glob_rec(&p, &t)
}

fn glob_rec(p: &[char], t: &[char]) -> bool {
    match p.split_first() {
        None => t.is_empty(),
        Some(('*', rest)) => {
            let (cross, rest) = match rest.split_first() {
                Some(('*', r)) => (true, r),
                _ => (false, rest),
            };
            (0..=t.len()).any(|i| {
                let (skipped, tail) = t.split_at(i);
                (cross || !skipped.contains(&'/')) && glob_rec(rest, tail)
            })
        }
        Some(('?', rest)) => {
            matches!(t.split_first(), Some((c, tail)) if *c != '/' && glob_rec(rest, tail))
        }
        Some((c, rest)) => {
            matches!(t.split_first(), Some((d, tail)) if d == c && glob_rec(rest, tail))
        }
    }
}

/// gcc accepts these and clang 18 rejects them with "unknown argument"
/// (each checked against clang 18.1.3). Unknown `-W` options only warn and
/// are silenced with `-Wno-unknown-warning-option` instead.
pub(crate) const GCC_ONLY_FLAGS: &[&str] = &[
    "-fconserve-stack",
    "-fipa-pta",
    "-fno-allow-store-data-races",
    "-fno-var-tracking-assignments",
    "-fvar-tracking",
    "-fno-ipa-cp-clone",
    "-fanalyzer",
    "-fno-gnu-unique",
];
pub(crate) const GCC_ONLY_PREFIXES: &[&str] = &["-flto-partition="];

/// Flags whose value is the next argument.
const TAKES_VALUE: &[&str] = &[
    "-I",
    "-D",
    "-U",
    "-include",
    "-imacros",
    "-isystem",
    "-iquote",
    "-idirafter",
    "-isysroot",
    "--sysroot",
    "-x",
    "-target",
    "-Xclang",
    "-Xpreprocessor",
];

/// Arguments for clang, without compiler name, source file, outputs or
/// dependency-file flags.
#[derive(Debug, Clone)]
pub(crate) struct ClangArgs {
    pub(crate) flags: Vec<String>,
    /// Every argument removed, in order, for the report.
    pub(crate) stripped: Vec<String>,
}

pub(crate) fn clang_args(entry: &Entry) -> Result<ClangArgs> {
    let mut flags = Vec::new();
    let mut stripped = Vec::new();
    let mut found_source = false;
    let mut it = entry.argv.iter().skip(1);
    while let Some(a) = it.next() {
        let a = a.as_str();
        if matches!(a, "-o" | "-MF" | "-MT" | "-MQ") {
            stripped.push(a.to_owned());
            if let Some(v) = it.next() {
                stripped.push(v.clone());
            }
            continue;
        }
        let output_or_dep = matches!(a, "-c" | "-M" | "-MM" | "-MD" | "-MMD" | "-MP" | "-MG")
            || a.starts_with("-Wp,-M")
            || (a.starts_with("-o") && a.len() > 2);
        let gcc_only =
            GCC_ONLY_FLAGS.contains(&a) || GCC_ONLY_PREFIXES.iter().any(|p| a.starts_with(p));
        if output_or_dep || gcc_only {
            stripped.push(a.to_owned());
            continue;
        }
        if TAKES_VALUE.contains(&a) {
            flags.push(a.to_owned());
            if let Some(v) = it.next() {
                flags.push(v.clone());
            }
            continue;
        }
        if !a.starts_with('-') && normalize(&entry.directory.join(a)) == entry.path {
            found_source = true;
            continue;
        }
        flags.push(a.to_owned());
    }
    if !found_source {
        bail!(
            "the command for {} does not name the file itself",
            entry.file
        );
    }
    flags.push("-Wno-unknown-warning-option".to_owned());
    flags.push("-fno-color-diagnostics".to_owned());
    Ok(ClangArgs { flags, stripped })
}

/// POSIX shell word splitting, enough for compilation databases: blanks,
/// single quotes, double quotes and backslash escapes.
pub(crate) fn shell_split(s: &str) -> Result<Vec<String>> {
    let mut words = Vec::new();
    let mut cur = String::new();
    let mut in_word = false;
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        match c {
            ' ' | '\t' | '\n' => {
                if in_word {
                    words.push(std::mem::take(&mut cur));
                    in_word = false;
                }
            }
            '\'' => {
                in_word = true;
                loop {
                    match chars.next() {
                        Some('\'') => break,
                        Some(x) => cur.push(x),
                        None => bail!("unterminated single quote"),
                    }
                }
            }
            '"' => {
                in_word = true;
                loop {
                    match chars.next() {
                        Some('"') => break,
                        Some('\\') => match chars.next() {
                            Some(x @ ('"' | '\\' | '$' | '`')) => cur.push(x),
                            Some('\n') => {}
                            Some(x) => {
                                cur.push('\\');
                                cur.push(x);
                            }
                            None => bail!("unterminated double quote"),
                        },
                        Some(x) => cur.push(x),
                        None => bail!("unterminated double quote"),
                    }
                }
            }
            '\\' => {
                in_word = true;
                match chars.next() {
                    Some('\n') | None => {}
                    Some(x) => cur.push(x),
                }
            }
            x => {
                in_word = true;
                cur.push(x);
            }
        }
    }
    if in_word {
        words.push(cur);
    }
    Ok(words)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splits_quotes_and_escapes() {
        let w = shell_split(r#"cc -DX="a b" -D'Y=1' a\ b.c "q\"x""#).unwrap();
        assert_eq!(w, ["cc", "-DX=a b", "-DY=1", "a b.c", "q\"x"]);
    }

    #[test]
    fn selects_by_prefix_and_glob() {
        assert!(glob_match("misc/*.c", "misc/bstr.c"));
        assert!(!glob_match("misc/*.c", "misc/sub/bstr.c"));
        assert!(glob_match("misc/**.c", "misc/sub/bstr.c"));
        assert!(glob_match("misc/b?tr.c", "misc/bstr.c"));
        let s = suffixes(Path::new("/x/.mpv/misc/bstr.c"));
        assert!(s.iter().any(|x| x.starts_with("misc/")));
    }

    #[test]
    fn strips_outputs_dependencies_and_gcc_only_flags() {
        let e = Entry {
            directory: PathBuf::from("/b"),
            file: "../s/a.c".into(),
            path: PathBuf::from("/s/a.c"),
            argv: shell_split("cc -I. -MD -MQ x.o -MF x.d -fconserve-stack -O2 -o x.o -c ../s/a.c")
                .unwrap(),
        };
        let a = clang_args(&e).unwrap();
        assert_eq!(
            a.flags,
            [
                "-I.",
                "-O2",
                "-Wno-unknown-warning-option",
                "-fno-color-diagnostics"
            ]
        );
        assert_eq!(
            a.stripped,
            [
                "-MD",
                "-MQ",
                "x.o",
                "-MF",
                "x.d",
                "-fconserve-stack",
                "-o",
                "x.o",
                "-c"
            ]
        );
    }
}
