//! End-to-end tests: small C files compiled through the real clang path.

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::compdb::{self, Entry};
use crate::frontend::{self, Loaded};
use crate::ir::Origin;
use crate::{dump, scan, survey};

static N: AtomicUsize = AtomicUsize::new(0);

/// Writes `files` into a fresh directory with a one-entry
/// `compile_commands.json` for `main.c`, gcc-style flags included.
fn fixture(files: &[(&str, &str)]) -> (PathBuf, Vec<Entry>) {
    let dir = std::env::temp_dir().join(format!(
        "achates-test-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    for (name, text) in files {
        std::fs::write(dir.join(name), text).unwrap();
    }
    let cmd = format!(
        r#"[{{"directory": "{}", "file": "main.c", "command": "cc -std=c11 -O2 -Wall -fconserve-stack -MD -MQ main.o -MF main.o.d -o main.o -c main.c"}}]"#,
        dir.display()
    );
    let db = dir.join("compile_commands.json");
    std::fs::write(&db, cmd).unwrap();
    let entries = compdb::load(&db).unwrap();
    (dir, entries)
}

fn load(files: &[(&str, &str)]) -> Loaded {
    let (_dir, entries) = fixture(files);
    let picked = compdb::select(&entries, "main.c").unwrap();
    frontend::load(picked.first().unwrap(), true).unwrap()
}

fn dump_of(src: &str, name: &str) -> String {
    let l = load(&[("main.c", src)]);
    let f =
        l.tu.functions
            .iter()
            .find(|f| f.name == name)
            .expect("function present");
    dump::function(f, &l.tu)
}

fn names(l: &Loaded) -> Vec<&str> {
    l.tu.functions
        .iter()
        .filter(|f| f.origin == Origin::MainFile)
        .map(|f| f.name.as_str())
        .collect()
}

fn header_names(l: &Loaded) -> Vec<(&str, Origin)> {
    l.tu.functions
        .iter()
        .filter(|f| f.origin != Origin::MainFile)
        .map(|f| (f.name.as_str(), f.origin))
        .collect()
}

/// Like [`fixture`], with one database entry per `(file, extra flags)`.
fn fixture_multi(files: &[(&str, &str)], units: &[(&str, &str)]) -> (PathBuf, Vec<Entry>) {
    let (dir, _) = fixture(files);
    let entries: Vec<String> = units
        .iter()
        .map(|(f, flags)| {
            format!(
                r#"{{"directory": "{}", "file": "{f}", "command": "cc -std=c11 -O2 {flags} -c {f}"}}"#,
                dir.display()
            )
        })
        .collect();
    let db = dir.join("compile_commands.json");
    std::fs::write(&db, format!("[{}]", entries.join(","))).unwrap();
    let entries = compdb::load(&db).unwrap();
    (dir, entries)
}

/// Asserts that `want` appear in `text` as consecutive lines, ignoring
/// leading indentation, so a test can pin down a subtree.
fn assert_lines(text: &str, want: &[&str]) {
    let lines: Vec<&str> = text.lines().map(str::trim_start).collect();
    let found = lines.windows(want.len()).any(|w| w == want);
    assert!(
        found,
        "expected consecutive lines\n{}\nin\n{text}",
        want.join("\n")
    );
}

#[test]
fn only_functions_defined_in_the_main_file_are_listed() {
    let header = "\
#define DEFINE_GETTER(n) int get_##n(void) { return n; }
#define BODY(x) ((x) * 2)
static inline int header_helper(int x) { return x + 1; }
static inline int header_helper2(int x) { return BODY(x); }
static inline int never_called(void) { return 0; }
";
    let main = "\
int before(int a) { return a; }
#include \"h.h\"
int after(int a) { return header_helper(a) + BODY(a); }
static int seven = 7;
DEFINE_GETTER(seven)
int last(void) { return header_helper2(1); }
";
    let l = load(&[("h.h", header), ("main.c", main)]);
    assert_eq!(names(&l), ["before", "after", "get_seven", "last"]);
    assert_eq!(
        header_names(&l),
        [
            ("header_helper", Origin::ProjectHeader),
            ("header_helper2", Origin::ProjectHeader)
        ]
    );
    let after = l.tu.functions.iter().find(|f| f.name == "after").unwrap();
    assert_eq!(after.lines, 1);
    assert_eq!(after.loc.as_ref().unwrap().line, 3);
}

#[test]
fn char_plus_char_is_promoted_to_int() {
    let d = dump_of("int f(char a, char b) { return a + b; }", "f");
    assert_lines(
        &d,
        &[
            "return",
            "binary + : int:i32",
            "implicit-cast IntegralCast : int:i32",
            "implicit-cast LValueToRValue : char:i8",
            "var param a (#0) : char:i8 lvalue",
            "implicit-cast IntegralCast : int:i32",
            "implicit-cast LValueToRValue : char:i8",
            "var param b (#1) : char:i8 lvalue",
        ],
    );
}

#[test]
fn signed_unsigned_comparisons_show_the_usual_conversions() {
    let d = dump_of(
        "int f(int a, unsigned b, long c, unsigned short s) { return (a < b) + (c < b) + (s < a); }",
        "f",
    );
    assert_lines(
        &d,
        &[
            "binary < : int:i32",
            "implicit-cast IntegralCast : unsigned int:u32",
            "implicit-cast LValueToRValue : int:i32",
            "var param a (#0) : int:i32 lvalue",
            "implicit-cast LValueToRValue : unsigned int:u32",
        ],
    );
    assert_lines(
        &d,
        &[
            "binary < : int:i32",
            "implicit-cast LValueToRValue : long:i64",
            "var param c (#2) : long:i64 lvalue",
            "implicit-cast IntegralCast : long:i64",
            "implicit-cast LValueToRValue : unsigned int:u32",
        ],
    );
    assert_lines(
        &d,
        &[
            "binary < : int:i32",
            "implicit-cast IntegralCast : int:i32",
            "implicit-cast LValueToRValue : unsigned short:u16",
        ],
    );
}

#[test]
fn logical_and_keeps_its_short_circuit_shape() {
    let d = dump_of("int g(void); int f(int *p) { return p && *p && g(); }", "f");
    assert_lines(
        &d,
        &[
            "return",
            "logical && (rhs only if lhs nonzero) : int:i32",
            "logical && (rhs only if lhs nonzero) : int:i32",
            "implicit-cast LValueToRValue : ptr<int:i32>",
        ],
    );
    assert_lines(
        &d,
        &[
            "call direct g : int:i32",
            "implicit-cast FunctionToPointerDecay : ptr<fn() -> int:i32>",
        ],
    );
}

#[test]
fn for_loop_with_continue() {
    let d = dump_of(
        "int f(int n) { int s = 0; for (int i = 0; i < n; i++) { if (i % 2) continue; s += i; } return s; }",
        "f",
    );
    assert_lines(
        &d,
        &[
            "for",
            "init:",
            "decl",
            "local i#2 : int:i32",
            "init:",
            "int 0 : int:i32",
            "cond:",
        ],
    );
    assert_lines(
        &d,
        &[
            "inc:",
            "unary post++ : int:i32",
            "var local i#2 : int:i32 lvalue",
            "body:",
        ],
    );
    assert_lines(&d, &["then:", "continue"]);
    assert_lines(
        &d,
        &[
            "compound-assign += : int:i32",
            "computed-as int:i32 -> int:i32",
            "var local s#1 : int:i32 lvalue",
        ],
    );
}

#[test]
fn switch_keeps_fallthrough_between_cases() {
    let d = dump_of(
        "int f(int x) { int r = 0; switch (x) { case 1: r += 1; case 2: r += 2; break; default: r = -1; } return r; }",
        "f",
    );
    assert_lines(&d, &["switch", "cond:"]);
    // `case 1` holds only its first statement; the next case follows as a
    // sibling, so control falls from one into the other.
    assert_lines(
        &d,
        &[
            "case",
            "label:",
            "int 1 : int:i32",
            "then:",
            "compound-assign += : int:i32",
        ],
    );
    assert_lines(
        &d,
        &["int 1 : int:i32", "case", "label:", "int 2 : int:i32"],
    );
    assert_lines(
        &d,
        &[
            "int 2 : int:i32",
            "break",
            "default",
            "then:",
            "assign = : int:i32",
        ],
    );
}

#[test]
fn goto_to_a_cleanup_label() {
    let d = dump_of(
        "void free(void *); void *malloc(unsigned long);\n\
         int f(int n) { int r = -1; void *p = malloc(n); if (!p) goto out; r = 0; free(p); out: return r; }",
        "f",
    );
    assert_lines(&d, &["then:", "goto out"]);
    assert_lines(&d, &["label out", "return"]);
}

#[test]
fn member_through_pointer_and_array_index() {
    let d = dump_of(
        "struct s { int x; int a[4]; }; int f(struct s *p, int i) { return p->x + p->a[i]; }",
        "f",
    );
    assert_lines(
        &d,
        &[
            "implicit-cast LValueToRValue : int:i32",
            "member ->x : int:i32 lvalue",
            "implicit-cast LValueToRValue : ptr<struct s>",
            "var param p (#0) : ptr<struct s> lvalue",
        ],
    );
    assert_lines(
        &d,
        &[
            "index : int:i32 lvalue",
            "implicit-cast ArrayToPointerDecay : ptr<int:i32>",
            "member ->a : array<int:i32; 4> lvalue",
        ],
    );
    assert_lines(
        &d,
        &[
            "struct s",
            "field x : int:i32",
            "field a : array<int:i32; 4>",
        ],
    );
}

#[test]
fn call_through_a_function_pointer() {
    let d = dump_of("int f(int (*fp)(int), int x) { return fp(x); }", "f");
    assert_lines(
        &d,
        &[
            "call indirect : int:i32",
            "implicit-cast LValueToRValue : ptr<fn(int:i32) -> int:i32>",
            "var param fp (#0) : ptr<fn(int:i32) -> int:i32> lvalue",
        ],
    );
}

#[test]
fn compound_literal_with_designators() {
    let d = dump_of(
        "struct p { int x, y; }; struct p f(int v) { return (struct p){ .y = v }; }",
        "f",
    );
    assert_lines(
        &d,
        &[
            "implicit-cast LValueToRValue : struct p",
            "compound-literal : struct p lvalue",
            "init-list : struct p",
            "zero-init : int:i32",
            "implicit-cast LValueToRValue : int:i32",
        ],
    );
}

#[test]
fn do_while_zero_macro_body() {
    let d = dump_of(
        "#define SWAP(a, b) do { int t_ = (a); (a) = (b); (b) = t_; } while (0)\n\
         void f(int *x, int *y) { SWAP(*x, *y); }",
        "f",
    );
    assert_lines(
        &d,
        &[
            "do-while",
            "body:",
            "compound",
            "decl",
            "local t_#1 : int:i32",
        ],
    );
    assert_lines(&d, &["cond:", "int 0 : int:i32"]);
}

#[test]
fn sizeof_is_clangs_constant_and_its_operand_is_not_evaluated() {
    let d = dump_of(
        "struct s { char c; double d; };\n\
         unsigned long f(int x) { return sizeof(x++) + sizeof(struct s) + _Alignof(struct s) + sizeof(char[3][5]); }",
        "f",
    );
    assert_lines(
        &d,
        &[
            "sizeof = 4 (operand not evaluated) : unsigned long:u64",
            "unary post++ : int:i32",
        ],
    );
    assert_lines(
        &d,
        &[
            "sizeof = 16 (operand not evaluated) : unsigned long:u64",
            "type struct s",
        ],
    );
    assert_lines(
        &d,
        &[
            "_Alignof = 8 (operand not evaluated) : unsigned long:u64",
            "type struct s",
        ],
    );
    assert_lines(
        &d,
        &["sizeof = 15 (operand not evaluated) : unsigned long:u64"],
    );
}

#[test]
fn variadic_argument_reads_are_represented_and_statement_expressions_are_not() {
    let src = "#include <stdarg.h>\n\
               int sum(int n, ...) { va_list ap; va_start(ap, n); int s = 0;\n\
               for (int i = 0; i < n; i++) s += va_arg(ap, int); va_end(ap); return s; }\n\
               int plain(int a) { return a; }\n\
               int gnu(int a) { return ({ int b = a; b + 1; }); }";
    let l = load(&[("main.c", src)]);
    let sum = l.tu.functions.iter().find(|f| f.name == "sum").unwrap();
    let u = scan::unsupported_of(sum, &l.tu);
    assert!(u.is_empty(), "{u:?}");
    let d = dump::function(sum, &l.tu);
    assert!(d.contains("va-arg : int:i32"), "{d}");

    let (_dir, entries) = fixture(&[("main.c", src)]);
    let s = survey::run(&compdb::select(&entries, "main.c").unwrap(), true).unwrap();
    let status: Vec<(&str, bool)> = s
        .rows
        .iter()
        .map(|r| (r.name.as_str(), r.counts.is_empty()))
        .collect();
    assert_eq!(status, [("sum", true), ("plain", true), ("gnu", false)]);
    let text = survey::render(&s);
    assert!(
        text.contains("total: 2 of 3 functions fully represented"),
        "{text}"
    );
    assert!(
        text.contains("StmtExpr: GNU statement expression"),
        "{text}"
    );
    assert!(
        text.contains("gcc-only flags removed: -fconserve-stack"),
        "{text}"
    );
}

#[test]
fn enums_globals_and_literals() {
    let d = dump_of(
        "enum e { A, B = 5, C, D = -1 }; enum u { X = 1u << 31 };\n\
         static const char *names[] = { \"a\\n\", \"b\" }; double k = 0.1;\n\
         int f(enum e v, enum u w) { return v == C ? names[1][0] + (int)k : (int)w + 'q'; }",
        "f",
    );
    assert_lines(&d, &["enum-constant C = 6 : int:i32"]);
    assert_lines(
        &d,
        &["enum e : int:i32", "A = 0", "B = 5", "C = 6", "D = -1"],
    );
    assert_lines(&d, &["enum u : unsigned int:u32"]);
    assert!(
        d.contains("global names : array<ptr<const char:i8>; 2> static"),
        "{d}"
    );
    assert!(
        d.contains("string \"a\\n\" : array<char:i8; 3> lvalue"),
        "{d}"
    );
    assert!(
        d.contains("float 0.10000000000000001 (bits 0x3fb999999999999a) : double:f64"),
        "{d}"
    );
    assert!(d.contains("char 113 : int:i32"), "{d}");
}

#[test]
fn a_clang_failure_is_an_error_naming_the_file() {
    let (_dir, entries) = fixture(&[("main.c", "int f(void) { return undeclared; }")]);
    let e = frontend::load(
        compdb::select(&entries, "main.c").unwrap().first().unwrap(),
        true,
    )
    .unwrap_err();
    let msg = format!("{e:#}");
    assert!(
        msg.contains("main.c") && msg.contains("undeclared"),
        "{msg}"
    );
}

#[test]
fn constructs_achates_does_not_represent_are_reported_in_place() {
    let src = "\
#include <stddef.h>
struct pt { int x, y; };
struct { int a; } anon_global;
int ok_fn(int a) { return a; }
long double ld(long double x) { return x; }
int vla(int n) { int a[n]; a[0] = 1; return a[0]; }
int elvis(int a, int b) { return a ?: b; }
void asm_fn(void) { __asm__ volatile(\"\" ::: \"memory\"); }
int local_struct(void) { struct loc { int q; } l = {1}; return l.q; }
int generic(int x) { return _Generic(x, int: 1, default: 2); }
int wide(void) { return L\"w\"[0]; }
int range(int x) { switch (x) { case 1 ... 3: return 1; } return 0; }
int computed(int i) { static void *t[] = { &&a, &&b }; goto *t[i]; a: return 1; b: return 2; }
unsigned long anon_size(void) { return sizeof anon_global; }
unsigned long off(void) { return offsetof(struct pt, y); }
int local_size(void) { struct loc2 { int q; } l = {0}; return sizeof l; }
int literal_anon(void) { return (struct { int z; }){ 3 }.z; }
void cleanup_fn(void) { void done(int *); int v __attribute__((cleanup(done))) = 0; (void)v; }
";
    let (_dir, entries) = fixture(&[("main.c", src)]);
    let s = survey::run(&compdb::select(&entries, "main.c").unwrap(), true).unwrap();
    let expect = [
        ("ok_fn", ""),
        ("ld", "type"),
        ("vla", "type"),
        ("elvis", "BinaryConditionalOperator"),
        ("asm_fn", "GCCAsmStmt"),
        ("local_struct", "RecordDecl"),
        ("generic", "GenericSelectionExpr"),
        ("wide", "StringLiteral"),
        ("range", "CaseStmt"),
        ("computed", "AddrLabelExpr"),
        ("anon_size", "UnaryExprOrTypeTraitExpr"),
        ("off", "OffsetOfExpr"),
        ("cleanup_fn", "VarDecl"),
        ("literal_anon", "type"),
    ];
    for (name, kind) in expect {
        let row = s
            .rows
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("{name} missing"));
        if kind.is_empty() {
            assert!(row.counts.is_empty(), "{name}: {:?}", row.counts);
        } else {
            assert!(
                row.counts.keys().any(|(k, _)| k == kind),
                "{name}: expected {kind}, got {:?}",
                row.counts
            );
        }
    }
    // clang rejects `sizeof(struct loc2)` at file scope, so the probe for it
    // fails alone and the other probes still get answers.
    let local = s.rows.iter().find(|r| r.name == "local_size").unwrap();
    assert!(
        local
            .counts
            .keys()
            .any(|(k, why)| k == "UnaryExprOrTypeTraitExpr"
                && why.starts_with("clang could not evaluate it")),
        "{:?}",
        local.counts
    );
    let computed = s.rows.iter().find(|r| r.name == "computed").unwrap();
    assert!(
        computed.counts.keys().any(|(k, _)| k == "IndirectGotoStmt"),
        "{:?}",
        computed.counts
    );
}

#[test]
fn sizeof_a_typedef_named_anonymous_struct() {
    let d = dump_of(
        "typedef struct { int a; char b; } T;\nunsigned long f(T *p) { return sizeof(T) + sizeof *p; }",
        "f",
    );
    assert_lines(
        &d,
        &[
            "sizeof = 8 (operand not evaluated) : unsigned long:u64",
            "type struct (typedef T)",
        ],
    );
    assert_lines(
        &d,
        &[
            "sizeof = 8 (operand not evaluated) : unsigned long:u64",
            "unary deref * : struct (typedef T) lvalue",
        ],
    );
}

#[test]
fn reachable_header_functions_are_added_transitively() {
    let header = "\
static inline int leaf(int x) { return x * 2; }
static inline int mid(int x) { return leaf(x) + 1; }
static inline int unused(int x) { return leaf(x); }
";
    let main = "#include \"h.h\"\nint top(int a) { return mid(a); }\n";
    let l = load(&[("h.h", header), ("main.c", main)]);
    assert_eq!(
        header_names(&l),
        [
            ("mid", Origin::ProjectHeader),
            ("leaf", Origin::ProjectHeader)
        ]
    );
    let top = l.tu.functions.iter().find(|f| f.name == "top").unwrap();
    let d = dump::function(top, &l.tu);
    assert!(d.contains("reaches header functions: leaf, mid"), "{d}");
    let leaf = l.tu.functions.iter().find(|f| f.name == "leaf").unwrap();
    assert!(leaf.def_file.ends_with("/h.h"), "{}", leaf.def_file);
    assert!(dump::function(leaf, &l.tu).contains("defined in project header"));

    let (_dir, entries) = fixture(&[("h.h", header), ("main.c", main)]);
    let picked = compdb::select(&entries, "main.c").unwrap();
    let without = frontend::load(picked.first().unwrap(), false).unwrap();
    assert!(header_names(&without).is_empty());
}

#[test]
fn glibc_inlines_are_system_header_functions() {
    let main = "#include <stdlib.h>\n\
                static int cmp(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }\n\
                int *find(int *v, unsigned long n, int k) { return bsearch(&k, v, n, sizeof *v, cmp); }\n";
    let l = load(&[("main.c", main)]);
    assert!(
        header_names(&l).contains(&("bsearch", Origin::SystemHeader)),
        "{:?}",
        header_names(&l)
    );
}

#[test]
fn a_header_function_reached_from_two_units_is_one_definition() {
    let header =
        "static inline int shared(int x) { return x + 1; }\nint other(int);\nint ext_fn(int);\n";
    let a = "#include \"h.h\"\nint one(int x) { return shared(x) + other(x) + ext_fn(x); }\n";
    let b = "#include \"h.h\"\nint other(int x) { return shared(shared(x)) + ext_fn(1); }\n";
    let (_dir, entries) = fixture_multi(
        &[("h.h", header), ("a.c", a), ("b.c", b)],
        &[("a.c", ""), ("b.c", "")],
    );
    let s = survey::run(&compdb::select(&entries, "*.c").unwrap(), true).unwrap();
    assert_eq!(s.rows.len(), 2);
    assert_eq!(s.headers.len(), 1);
    let h = s.headers.values().next().unwrap();
    assert_eq!((h.sites_from_selected, h.reached_by), (3, 2));
    // `other` is defined in the selection; `ext_fn` is not.
    assert_eq!(s.externals.keys().collect::<Vec<_>>(), ["ext_fn"]);
    let ext = s.externals.get("ext_fn").unwrap();
    assert_eq!((ext.selected_callers.len(), ext.sites), (2, 2));
    let text = survey::render(&s);
    assert!(
        text.contains("external functions: 1 named but defined nowhere in the selection"),
        "{text}"
    );
    assert!(
        text.contains("project header: 1 reachable, 1 fully represented, named at 3 places"),
        "{text}"
    );
}

#[test]
fn two_bodies_under_one_identity_are_an_error() {
    let header = "static inline int k(void) { return V; }\n";
    let a = "#include \"h.h\"\nint fa(void) { return k(); }\n";
    let b = "#include \"h.h\"\nint fb(void) { return k(); }\n";
    let (_dir, entries) = fixture_multi(
        &[("h.h", header), ("a.c", a), ("b.c", b)],
        &[("a.c", "-DV=1"), ("b.c", "-DV=2")],
    );
    let e = survey::run(&compdb::select(&entries, "*.c").unwrap(), true).unwrap_err();
    let msg = format!("{e:#}");
    assert!(
        msg.contains("`k`") && msg.contains("different bodies"),
        "{msg}"
    );
}

#[test]
fn an_unsupported_header_function_fails_only_the_strict_figure() {
    let header = "static inline int gnu(int a) { return ({ int b = a; b + 1; }); }\n";
    let main =
        "#include \"h.h\"\nint caller(int a) { return gnu(a); }\nint alone(int a) { return a; }\n";
    let (_dir, entries) = fixture(&[("h.h", header), ("main.c", main)]);
    let s = survey::run(&compdb::select(&entries, "main.c").unwrap(), true).unwrap();
    let caller = s.rows.iter().find(|r| r.name == "caller").unwrap();
    assert!(caller.counts.is_empty(), "{:?}", caller.counts);
    assert!(!s.strictly_ok(caller));
    assert!(s.strictly_ok(s.rows.iter().find(|r| r.name == "alone").unwrap()));
    let text = survey::render(&s);
    assert!(
        text.contains("total: 2 of 2 functions fully represented"),
        "{text}"
    );
    assert!(
        text.contains("1 of 2 functions fully represented together with every header function"),
        "{text}"
    );
    assert!(
        text.contains("project header: 1 reachable, 0 fully represented"),
        "{text}"
    );
}
