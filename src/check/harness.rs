//! The two programs that run one function on the generated inputs: a Lean
//! module that calls the emitted definition, and a C file that calls the
//! compiled function. Both are written from the same [`Plan`], read the
//! same tokens and print results in the same form, so that agreement is
//! equality of lines.

use std::fmt::Write as _;

use crate::check::format;
use crate::check::shape::{Plan, Shape};
use crate::emit::names::int_ty;
use crate::types::FloatKind;

/// Rounds each loop of the model may run. An input that needs more ends
/// as `fuel`, which counts as a failed check: it is a limit of the check,
/// and says nothing about the C. A million rounds made one function of
/// `misc/` take hours on inputs that ask for billions of rounds.
pub(crate) const FUEL: u64 = 100_000;

/// Seconds one call may take in the C harness before it counts as looping
/// for ever.
pub(crate) const CK_SECONDS: u64 = 10;

fn lean_ty(s: &Shape) -> String {
    match s {
        Shape::Bool => "Bool".into(),
        Shape::Int { ty, .. } => int_ty(*ty),
        Shape::Float(FloatKind::Float) => "F32".into(),
        Shape::Float(FloatKind::Double) => "F64".into(),
        Shape::Bstr | Shape::Struct { .. } | Shape::Array { .. } => "Agg".into(),
        Shape::CStr
        | Shape::TallocCtx
        | Shape::Slot { .. }
        | Shape::Ptr { .. }
        | Shape::Format
        | Shape::VaList => "Ptr".into(),
    }
}

/// The Lean term that reads one format argument and the `VArg` it is.
fn lean_format_arg(a: format::Arg, x: &str) -> (String, String) {
    match a {
        format::Arg::Double => ("f64".into(), format!("VArg.f64 {x}")),
        format::Arg::Str => ("cstr".into(), format!("VArg.ptr \"char\" {x}")),
        _ => {
            let (bits, signed) = a.int().unwrap_or((32, true));
            let (rd, con) = if signed {
                ("sint", "sint")
            } else {
                ("uint", "uint")
            };
            (
                format!("{rd} {bits}"),
                format!("VArg.{con} \"{}\" {x}", a.rank()),
            )
        }
    }
}

fn is_agg(s: &Shape) -> bool {
    matches!(s, Shape::Bstr | Shape::Struct { .. } | Shape::Array { .. })
}

#[derive(Debug, Default)]
struct Lean {
    defs: String,
    n: usize,
}

impl Lean {
    fn def(&mut self, prefix: &str, sig: &str, body: &str) -> String {
        let name = format!("{prefix}{}", self.n);
        self.n += 1;
        let _ = writeln!(self.defs, "def {name} {sig} := do\n{body}\n");
        name
    }

    /// `owned` says the value sits in an object the function may write
    /// through, so a buffer in it comes from talloc, as mpv's own do.
    fn reader(&mut self, s: &Shape, owned: bool) -> String {
        let ty = lean_ty(s);
        let body = match s {
            Shape::Bool => "  bool".to_owned(),
            Shape::Int { ty, .. } => {
                format!("  {} {}", if ty.signed { "sint" } else { "uint" }, ty.bits)
            }
            Shape::Float(FloatKind::Float) => "  f32".to_owned(),
            Shape::Float(FloatKind::Double) => "  f64".to_owned(),
            Shape::Bstr => format!("  bstr {owned}"),
            Shape::CStr => "  cstr".to_owned(),
            Shape::TallocCtx => "  tallocCtx".to_owned(),
            Shape::Slot { .. } => "  pure Ptr.null".to_owned(),
            Shape::VaList => "  vaList".to_owned(),
            Shape::Format => {
                let mut b = String::from("  match ← fmtIndex with\n");
                for (k, f) in format::PRINTF.iter().enumerate() {
                    let bytes: Vec<String> = f.bytes().map(|x| x.to_string()).collect();
                    let _ = writeln!(
                        b,
                        "  | {k} => do\n    let p ← fmtString [{}]",
                        bytes.join(", ")
                    );
                    let mut vargs = Vec::new();
                    for (i, a) in format::printf_args(f).into_iter().enumerate() {
                        let (rd, v) = lean_format_arg(a, &format!("x{i}"));
                        let _ = writeln!(b, "    let x{i} ← {rd}");
                        vargs.push(format!("({v})"));
                    }
                    let _ = writeln!(b, "    setVargs [{}]\n    pure p", vargs.join(", "));
                }
                b.push_str("  | _ => bad \"format index\"");
                b
            }
            Shape::Struct { size, fields, .. } => {
                let mut b = format!("  let mut a := Agg'.zero {size}\n");
                for f in fields {
                    let r = self.reader(&f.shape, owned);
                    let put = if is_agg(&f.shape) { "putAgg" } else { "put" };
                    let _ = writeln!(b, "  a := Agg'.{put} a {} (← {r})", f.offset);
                }
                b.push_str("  pure a");
                b
            }
            Shape::Array {
                elem,
                len,
                elem_size,
            } => {
                let r = self.reader(elem, owned);
                format!(
                    "  let mut a := Agg'.zero {}\n  for i in List.range {len} do\n    a := Agg'.put a (i * {elem_size}) (← {r})\n  pure a",
                    len * elem_size
                )
            }
            Shape::Ptr {
                pointee,
                size,
                align,
            } => {
                let r = self.reader(pointee, true);
                let bytes = if is_agg(pointee) {
                    format!("(← {r}).bytes")
                } else {
                    format!("CVal.encode (← {r})")
                };
                format!("  pointee {size} {align} (do pure ({bytes}))")
            }
        };
        self.def("rd", &format!(": H {ty}"), &body)
    }

    fn observer(&mut self, s: &Shape) -> String {
        let ty = lean_ty(s);
        let body = match s {
            Shape::Bool => "  pure (if v then \"1\" else \"0\")".to_owned(),
            Shape::Int { .. } => "  pure (toString v)".to_owned(),
            Shape::Float(FloatKind::Float) => "  pure (obsFloat32 v)".to_owned(),
            Shape::Float(FloatKind::Double) => "  pure (obsFloat v)".to_owned(),
            Shape::Bstr => "  obsBstr v".to_owned(),
            Shape::CStr => "  obsCStr v".to_owned(),
            Shape::TallocCtx | Shape::Slot { .. } | Shape::Format | Shape::VaList => {
                "  obsPtr v".to_owned()
            }
            Shape::Struct { fields, .. } => {
                let mut b = String::from("  observe do\n    let mut out := \"{\"\n");
                for (i, f) in fields.iter().enumerate() {
                    let o = self.observer(&f.shape);
                    let sep = if i == 0 { "" } else { "\",\" ++ " };
                    let val = if is_agg(&f.shape) {
                        format!("(Agg.sub v {} {})", f.offset, f.size)
                    } else {
                        let t = lean_ty(&f.shape);
                        format!("(← (liftExcept (Agg.get {t} v {}) : M {t}))", f.offset)
                    };
                    let _ = writeln!(b, "    out := out ++ {sep}(← {o} {val})");
                }
                b.push_str("    pure (out ++ \"}\")");
                b
            }
            Shape::Array {
                elem,
                len,
                elem_size,
            } => {
                let o = self.observer(elem);
                let t = lean_ty(elem);
                format!(
                    "  observe do\n    let mut out := \"[\"\n    for i in List.range {len} do\n      out := out ++ (← {o} (← (liftExcept (Agg.get {t} v (i * {elem_size})) : M {t}))) ++ \",\"\n    pure (out ++ \"]\")"
                )
            }
            Shape::Ptr {
                pointee,
                size,
                align,
            } => {
                let o = self.observer(pointee);
                let load = if is_agg(pointee) {
                    format!("(Mem.loadAgg v {size} {align} : M Agg)")
                } else {
                    let t = lean_ty(pointee);
                    format!("(Mem.load {t} v : M {t})")
                };
                format!(
                    "  observe do\n    if v == .null then pure \"null\"\n    else\n      let x ← {load}\n      pure (\"*\" ++ (← {o} x))"
                )
            }
        };
        self.def("ob", &format!("(v : {ty}) : H String"), &body)
    }
}

/// The Lean module that runs `lean_name` on one input line.
pub(crate) fn lean_module(
    root: &str,
    module: &str,
    lean_name: &str,
    plan: &Plan,
    instances: bool,
) -> String {
    let mut g = Lean::default();
    let mut run = String::from("def run : H String := do\n");
    let mut args = String::new();
    let mut after = String::new();
    for (i, (_, s)) in plan.params.iter().enumerate() {
        let r = g.reader(s, false);
        let _ = writeln!(run, "  let a{i} ← {r}");
        let _ = write!(args, " a{i}");
        if matches!(s, Shape::Ptr { .. }) {
            let o = g.observer(s);
            let _ = writeln!(after, "    out := out ++ \" a{i}=\" ++ (← {o} a{i})");
        }
    }
    if plan.variadic {
        run.push_str("  let va := (← get).vargs\n");
        args.push_str(" va");
    }
    let ret = plan.ret.as_ref().map(|s| g.observer(s));
    let _ = writeln!(
        run,
        "  match ← call ({lean_name} {FUEL}{args}) with\n  | .error e => pure (renderErr e)\n  | .ok r =>\n    let mut out := \"ok\""
    );
    if let Some(o) = ret {
        let _ = writeln!(run, "    out := out ++ \" ret=\" ++ (← {o} r)");
    }
    run.push_str(&after);
    run.push_str("    out := out ++ (← obsInputs)\n    pure out\n");
    let inst = if instances {
        "import Check.Instances\n"
    } else {
        ""
    };
    format!(
        "import {root}\nimport AchatesCheck\n{inst}\n/-! Written by `achates check`; do not edit. -/\n\nset_option linter.unusedVariables false\n\nopen Achates AchatesCheck\n\nnamespace Check.{module}\n\n{}{run}\nend Check.{module}\n",
        g.defs
    )
}

/// `Main.lean` of the driver: picks the function by its module name and
/// prints one result line per input line.
pub(crate) fn lean_main(root: &str, modules: &[String]) -> String {
    let mut s = format!("import {root}\nimport AchatesCheck\n");
    for m in modules {
        let _ = writeln!(s, "import Check.{m}");
    }
    s.push_str("\n/-! Written by `achates check`; do not edit. -/\n\nopen Achates AchatesCheck\n\ndef pick (name : String) : Option (H String) :=\n  match name with\n");
    for m in modules {
        let _ = writeln!(s, "  | \"{m}\" => some Check.{m}.run");
    }
    let _ = write!(
        s,
        "  | _ => none\n\ndef main (args : List String) : IO UInt32 := do\n  let [name, path] := args | do\n    IO.eprintln \"usage: check FUNCTION INPUTS\"\n    return 2\n  let some body := pick name | do\n    IO.eprintln s!\"no function {{name}}\"\n    return 2\n  let m0 ← match ({root}.Statics.init.run {{}}) with\n    | .ok (_, m) => pure m\n    | .error e => do\n      IO.eprintln s!\"static initialisation failed: {{renderErr e}}\"\n      return 2\n  let out ← IO.getStdout\n  for line in ← IO.FS.lines path do\n    let toks := (line.splitOn \" \").filter (· != \"\")\n    match toks with\n    | idx :: rest =>\n      out.putStrLn s!\"{{idx}} {{runCase m0 rest.toArray body}}\"\n      out.flush\n    | [] => pure ()\n  return 0\n"
    );
    s
}

/// Helpers every C harness has. `CK_BSTR` and `CK_TALLOC` add the parts
/// that need mpv's `bstr` and talloc headers.
const C_RUNTIME: &str = r#"
#include <inttypes.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

enum { CK_BUF, CK_TALLOC_BUF, CK_OBJ, CK_CTX };
struct ck_in { const unsigned char *base; size_t size; int kind; };
static struct ck_in ck_ins[256];
static int ck_ninputs;
static char *ck_pos;
static long long ck_max_ms;
/* The format the input chose, for a function that takes printf arguments. */
static int ck_fmt;

static void ck_die(const char *msg)
{
    fprintf(stderr, "check harness: %s\n", msg);
    exit(3);
}

static const char *ck_tok(void)
{
    while (*ck_pos == ' ')
        ck_pos++;
    if (!*ck_pos)
        ck_die("input line is too short");
    char *t = ck_pos;
    while (*ck_pos && *ck_pos != ' ')
        ck_pos++;
    if (*ck_pos)
        *ck_pos++ = 0;
    return t;
}

static long long ck_sint(void) { return strtoll(ck_tok(), NULL, 10); }
static unsigned long long ck_uint(void) { return strtoull(ck_tok(), NULL, 10); }

static double ck_f64(void)
{
    uint64_t bits = strtoull(ck_tok(), NULL, 16);
    double d;
    memcpy(&d, &bits, sizeof d);
    return d;
}

static float ck_f32(void)
{
    uint32_t bits = (uint32_t)strtoul(ck_tok(), NULL, 16);
    float f;
    memcpy(&f, &bits, sizeof f);
    return f;
}

static void ck_reg(const void *p, size_t size, int kind)
{
    if (ck_ninputs == 256)
        ck_die("too many input objects");
    ck_ins[ck_ninputs++] = (struct ck_in){p, size, kind};
}

static int ck_hex(char c) { return c <= '9' ? c - '0' : c - 'a' + 10; }

#ifdef CK_TALLOC
#include "ta/ta.h"
#endif

/* `N` is the null pointer; `H<hex>` is a buffer of exactly those bytes,
   plus a terminator when `nul`, and `H<hex>:<k>` the same with k bytes of
   uninitialised room after them when it is a talloc buffer. */
static void *ck_buf(int talloc, int nul, size_t *len)
{
    const char *t = ck_tok();
    *len = 0;
    if (t[0] == 'N')
        return NULL;
    const char *colon = strchr(t, ':');
    size_t n = (colon ? (size_t)(colon - t - 1) : strlen(t + 1)) / 2;
    size_t size = n + (nul ? 1 : 0);
    unsigned char *p;
#ifdef CK_TALLOC
    /* `:<k>` gives a talloc buffer k bytes of room past its contents. */
    if (talloc && colon)
        size += strtoull(colon + 1, NULL, 10);
    if (talloc)
        p = ta_alloc_size(NULL, size);
    else
#endif
        p = malloc(size ? size : 1);
    if (!p)
        ck_die("out of memory");
    for (size_t i = 0; i < n; i++)
        p[i] = (unsigned char)(ck_hex(t[1 + 2 * i]) * 16 + ck_hex(t[2 + 2 * i]));
    if (nul)
        p[n] = 0;
    ck_reg(p, size, talloc ? CK_TALLOC_BUF : CK_BUF);
    *len = n;
    return p;
}

static char *ck_cstr(void)
{
    size_t n;
    return ck_buf(0, 1, &n);
}

#ifdef CK_TALLOC
static void *ck_ctx(void)
{
    const char *t = ck_tok();
    if (t[0] == 'N')
        return NULL;
    void *p = ta_alloc_size(NULL, 0);
    ck_reg(p, 0, CK_CTX);
    return p;
}
#endif

/* Prints where `p` points relative to the inputs and returns 1, or returns
   0 for a pointer to anything else. The start of a talloc buffer counts as
   anything else: realloc may or may not have moved it. */
static int ck_loc(const void *p)
{
    const unsigned char *q = p;
    if (!q) {
        fputs("null", stdout);
        return 1;
    }
    for (int i = 0; i < ck_ninputs; i++) {
        const struct ck_in *in = &ck_ins[i];
        if (q >= in->base && q <= in->base + in->size) {
            if (in->kind == CK_TALLOC_BUF && q == in->base)
                return 0;
            printf("in%d+%td", i, q - in->base);
            return 1;
        }
    }
    return 0;
}

static int ck_kind(const void *p)
{
    const unsigned char *q = p;
    for (int i = 0; q && i < ck_ninputs; i++) {
        if (q >= ck_ins[i].base && q <= ck_ins[i].base + ck_ins[i].size)
            return ck_ins[i].kind;
    }
    return -1;
}

static void ck_bytes(const unsigned char *p, size_t n)
{
    for (size_t i = 0; i < n; i++)
        printf("%02x", p[i]);
}

static void ck_obs_ptr(const void *p)
{
    if (!ck_loc(p))
        fputs("other", stdout);
}

static void ck_obs_cstr(const char *p)
{
    if (ck_loc(p))
        return;
    fputs("str:", stdout);
    ck_bytes((const unsigned char *)p, strlen(p));
}

static void ck_obs_f64(double d)
{
    uint64_t bits;
    memcpy(&bits, &d, sizeof bits);
    printf("D%" PRIu64, bits);
}

static void ck_obs_f32(float f)
{
    uint32_t bits;
    memcpy(&bits, &f, sizeof bits);
    printf("S%" PRIu32, bits);
}

#ifdef CK_BSTR
static struct bstr ck_bstr(int talloc)
{
    size_t n;
    unsigned char *p = ck_buf(talloc, 0, &n);
    return (struct bstr){p, n};
}

static void ck_obs_bstr(struct bstr b)
{
    fputs("bstr(", stdout);
    if (ck_loc(b.start)) {
        printf(",%zu", b.len);
        if (ck_kind(b.start) == CK_TALLOC_BUF) {
            putchar(',');
            ck_bytes(b.start, b.len);
        }
    } else {
        printf("new,%zu,", b.len);
        ck_bytes(b.start, b.len);
    }
    putchar(')');
}
#endif

static void ck_obs_inputs(void)
{
    for (int i = 0; i < ck_ninputs; i++) {
        if (ck_ins[i].kind != CK_BUF)
            continue;
        printf(" in%d=", i);
        ck_bytes(ck_ins[i].base, ck_ins[i].size);
    }
}

static void ck_case(int expect_abort);

/* Each input line is `INDEX MODE TOKENS`. Mode `R` runs the call and prints
   what it left; mode `A` runs it in a child process and prints whether the
   child died from abort(), for inputs on which the model stops at a failed
   assertion or an abort. */
int main(int argc, char **argv)
{
    if (argc != 2)
        ck_die("usage: harness INPUTS");
    FILE *f = fopen(argv[1], "r");
    if (!f)
        ck_die("cannot open the input file");
    char *line = NULL;
    size_t cap = 0;
    while (getline(&line, &cap, f) >= 0) {
        size_t n = strlen(line);
        if (n && line[n - 1] == '\n')
            line[n - 1] = 0;
        ck_pos = line;
        ck_ninputs = 0;
        const char *idx = ck_tok();
        const char *mode = ck_tok();
        printf("%s ", idx);
        /* A call that runs this long is taken to loop for ever: SIGALRM
           ends the harness, and the input is reported as a crash. */
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        alarm(CK_SECONDS);
        ck_case(mode[0] == 'A');
        alarm(0);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        long long ms = (t1.tv_sec - t0.tv_sec) * 1000LL + (t1.tv_nsec - t0.tv_nsec) / 1000000;
        if (ms > ck_max_ms)
            ck_max_ms = ms;
        putchar('\n');
        /* One line per input reaches the pipe before the next call, so a
           crash is pinned to its input. */
        fflush(stdout);
        for (int i = 0; i < ck_ninputs; i++) {
            if (ck_ins[i].kind == CK_BUF || ck_ins[i].kind == CK_OBJ)
                free((void *)ck_ins[i].base);
#ifdef CK_TALLOC
            if (ck_ins[i].kind == CK_CTX)
                ta_free((void *)ck_ins[i].base);
#endif
        }
    }
    fprintf(stderr, "ck_max_ms=%lld\n", ck_max_ms);
    return 0;
}
"#;

#[derive(Debug, Default)]
struct C {
    defs: String,
    n: usize,
}

impl C {
    fn name(&mut self, prefix: &str) -> String {
        self.n += 1;
        format!("{prefix}{}", self.n - 1)
    }

    fn reader(&mut self, s: &Shape, owned: bool) -> String {
        let ty = s.c_type();
        let body = match s {
            Shape::Bool => "    return ck_uint() != 0;".to_owned(),
            Shape::Int { ty: i, c_type } => format!(
                "    return ({c_type}){}();",
                if i.signed { "ck_sint" } else { "ck_uint" }
            ),
            Shape::Float(FloatKind::Float) => "    return ck_f32();".to_owned(),
            Shape::Float(FloatKind::Double) => "    return ck_f64();".to_owned(),
            Shape::Bstr => format!("    return ck_bstr({});", u8::from(owned)),
            Shape::CStr => "    return ck_cstr();".to_owned(),
            Shape::TallocCtx => "    return ck_ctx();".to_owned(),
            Shape::Slot { .. } | Shape::VaList => "    return NULL;".to_owned(),
            Shape::Format => {
                let mut b = String::from(
                    "    const char *t = ck_tok();\n    ck_fmt = (int)strtol(t + 1, NULL, 10);\n    switch (ck_fmt) {\n",
                );
                for (k, f) in format::PRINTF.iter().enumerate() {
                    let _ = writeln!(b, "    case {k}: return {};", format::c_literal(f));
                }
                b.push_str("    }\n    ck_die(\"bad format index\");\n    return NULL;");
                b
            }
            Shape::Struct { fields, .. } => {
                let mut b = format!("    {ty} v;\n    memset(&v, 0, sizeof v);\n");
                for f in fields {
                    if let Shape::Array { elem, len, .. } = &f.shape {
                        let r = self.reader(elem, owned);
                        let _ = writeln!(
                            b,
                            "    for (int i = 0; i < {len}; i++)\n        v.{}[i] = {r}();",
                            f.name
                        );
                    } else {
                        let r = self.reader(&f.shape, owned);
                        let _ = writeln!(b, "    v.{} = {r}();", f.name);
                    }
                }
                b.push_str("    return v;");
                b
            }
            // Reached only through the struct case above.
            Shape::Array { elem, .. } => return self.reader(elem, owned),
            Shape::Ptr { pointee, .. } => {
                let r = self.reader(pointee, true);
                let t = pointee.c_type();
                format!(
                    "    const char *t = ck_tok();\n    if (t[0] == 'N')\n        return NULL;\n    {t} *p = malloc(sizeof({t}));\n    if (!p)\n        ck_die(\"out of memory\");\n    *p = {r}();\n    ck_reg(p, sizeof({t}), CK_OBJ);\n    return p;"
                )
            }
        };
        let name = self.name("rd");
        let _ = writeln!(self.defs, "static {ty} {name}(void)\n{{\n{body}\n}}\n");
        name
    }

    fn observer(&mut self, s: &Shape) -> String {
        let ty = s.c_type();
        let body = match s {
            Shape::Bool => "    printf(\"%d\", (int)v);".to_owned(),
            Shape::Int { ty: i, .. } => {
                if i.signed {
                    "    printf(\"%lld\", (long long)v);".to_owned()
                } else {
                    "    printf(\"%llu\", (unsigned long long)v);".to_owned()
                }
            }
            Shape::Float(FloatKind::Float) => "    ck_obs_f32(v);".to_owned(),
            Shape::Float(FloatKind::Double) => "    ck_obs_f64(v);".to_owned(),
            Shape::Bstr => "    ck_obs_bstr(v);".to_owned(),
            Shape::CStr => "    ck_obs_cstr(v);".to_owned(),
            Shape::TallocCtx | Shape::Slot { .. } | Shape::Format | Shape::VaList => {
                "    ck_obs_ptr(v);".to_owned()
            }
            Shape::Struct { fields, .. } => {
                let mut b = String::from("    putchar('{');\n");
                for (i, f) in fields.iter().enumerate() {
                    if i > 0 {
                        b.push_str("    putchar(',');\n");
                    }
                    if let Shape::Array { elem, len, .. } = &f.shape {
                        let o = self.observer(elem);
                        let _ = writeln!(
                            b,
                            "    putchar('[');\n    for (int i = 0; i < {len}; i++) {{\n        {o}(v.{}[i]);\n        putchar(',');\n    }}\n    putchar(']');",
                            f.name
                        );
                    } else {
                        let o = self.observer(&f.shape);
                        let _ = writeln!(b, "    {o}(v.{});", f.name);
                    }
                }
                b.push_str("    putchar('}');");
                b
            }
            Shape::Array { elem, .. } => return self.observer(elem),
            Shape::Ptr { pointee, .. } => {
                let o = self.observer(pointee);
                format!(
                    "    if (!v) {{\n        fputs(\"null\", stdout);\n        return;\n    }}\n    putchar('*');\n    {o}(*v);"
                )
            }
        };
        let name = self.name("ob");
        let _ = writeln!(self.defs, "static void {name}({ty} v)\n{{\n{body}\n}}\n");
        name
    }
}

/// The C file that calls `function`. `includes` are the files whose text
/// defines it, as absolute paths, in the order to include them.
pub(crate) fn c_harness(includes: &[String], function: &str, plan: &Plan) -> String {
    let mut g = C::default();
    let mut read = String::new();
    let mut args = Vec::new();
    let mut after = String::new();
    let mut decls = Vec::new();
    for (i, (_, s)) in plan.params.iter().enumerate() {
        if *s == Shape::VaList {
            continue;
        }
        let r = g.reader(s, false);
        let _ = writeln!(read, "    {} a{i} = {r}();", s.c_type());
        args.push(format!("a{i}"));
        decls.push(format!("{} a{i}", s.c_type()));
        if matches!(s, Shape::Ptr { .. }) {
            let o = g.observer(s);
            let _ = writeln!(after, "    fputs(\" a{i}=\", stdout);\n    {o}(a{i});");
        }
    }
    let formatted = plan.params.iter().any(|p| p.1 == Shape::Format);
    let call = if formatted {
        format!("ck_call({})", args.join(", "))
    } else {
        format!("{function}({})", args.join(", "))
    };
    let ret = plan.ret.as_ref().map(|s| (s.c_type(), g.observer(s)));
    // The harness uses POSIX (fork, alarm, clock_gettime), and the first
    // header anything includes fixes what the C library declares.
    let mut s = String::from(
        "#if !defined(_POSIX_C_SOURCE) && !defined(_GNU_SOURCE)\n#define _POSIX_C_SOURCE 200809L\n#endif\n",
    );
    for inc in includes {
        let _ = writeln!(s, "#include \"{inc}\"");
    }
    if plan.any(&|x| matches!(x, Shape::Bstr)) {
        s.push_str("#include \"misc/bstr.h\"\n#define CK_BSTR 1\n");
    }
    if plan.any(&|x| matches!(x, Shape::Bstr | Shape::TallocCtx)) {
        s.push_str("#define CK_TALLOC 1\n");
    }
    let _ = writeln!(s, "#define CK_SECONDS {CK_SECONDS}");
    s.push_str(C_RUNTIME);
    s.push('\n');
    s.push_str(&g.defs);
    if formatted {
        s.push_str(&c_format_call(function, plan, &args, &decls));
    }
    let _ = write!(
        s,
        "static void ck_case(int expect_abort)\n{{\n{read}    if (expect_abort) {{\n        fflush(stdout);\n        pid_t pid = fork();\n        if (pid < 0)\n            ck_die(\"fork failed\");\n        if (pid == 0) {{\n            alarm(CK_SECONDS - 1);\n            if (!freopen(\"/dev/null\", \"w\", stderr))\n                _exit(4);\n            (void){call};\n            _exit(0);\n        }}\n        int st = 0;\n        waitpid(pid, &st, 0);\n        if (WIFSIGNALED(st) && WTERMSIG(st) == SIGABRT)\n            fputs(\"aborted\", stdout);\n        else if (WIFSIGNALED(st) && WTERMSIG(st) == SIGALRM)\n            fputs(\"timeout\", stdout);\n        else if (WIFSIGNALED(st))\n            printf(\"signal %d\", WTERMSIG(st));\n        else\n            fputs(\"returned\", stdout);\n        return;\n    }}\n"
    );
    match &ret {
        Some((ty, o)) => {
            // The function may return `const char *`; the harness only reads it.
            let cast = if matches!(plan.ret, Some(Shape::CStr)) {
                "(char *)"
            } else {
                ""
            };
            let _ = writeln!(
                s,
                "    {ty} r = {cast}{call};\n    fputs(\"ok ret=\", stdout);\n    {o}(r);"
            );
        }
        None => {
            let _ = writeln!(s, "    {call};\n    fputs(\"ok\", stdout);");
        }
    }
    s.push_str(&after);
    s.push_str("    ck_obs_inputs();\n}\n");
    s
}

/// `ck_call`: reads the arguments the chosen format asks for and calls
/// the function with them, through `...` or through a `va_list` made by
/// `ck_vcall`.
fn c_format_call(function: &str, plan: &Plan, args: &[String], decls: &[String]) -> String {
    let ret = plan
        .ret
        .as_ref()
        .map_or_else(|| "void".to_owned(), Shape::c_type);
    let ret_kw = if ret == "void" { "" } else { "return " };
    let mut s = String::new();
    let target = if plan.variadic {
        function.to_owned()
    } else {
        let last = args.last().cloned().unwrap_or_default();
        let _ = write!(
            s,
            "static {ret} ck_vcall({}, ...)\n{{\n    va_list ap;\n    va_start(ap, {last});\n    {}{function}({}, ap);\n    va_end(ap);\n{}}}\n\n",
            decls.join(", "),
            if ret == "void" {
                String::new()
            } else {
                format!("{ret} r = ")
            },
            args.join(", "),
            if ret == "void" { "" } else { "    return r;\n" },
        );
        "ck_vcall".to_owned()
    };
    let _ = write!(
        s,
        "static {ret} ck_call({})\n{{\n    switch (ck_fmt) {{\n",
        decls.join(", ")
    );
    for (k, f) in format::PRINTF.iter().enumerate() {
        let _ = writeln!(s, "    case {k}: {{");
        let mut extra = Vec::new();
        for (i, a) in format::printf_args(f).into_iter().enumerate() {
            let read = match a {
                format::Arg::Double => "ck_f64()".to_owned(),
                format::Arg::Str => "ck_cstr()".to_owned(),
                _ if a.int().is_some_and(|x| x.1) => format!("({})ck_sint()", a.c_type()),
                _ => format!("({})ck_uint()", a.c_type()),
            };
            let _ = writeln!(s, "        {} x{i} = {read};", a.c_type());
            extra.push(format!("x{i}"));
        }
        let all: Vec<String> = args.iter().cloned().chain(extra).collect();
        let _ = writeln!(s, "        {ret_kw}{target}({});", all.join(", "));
        if ret == "void" {
            s.push_str("        return;\n");
        }
        s.push_str("    }\n");
    }
    s.push_str("    }\n    ck_die(\"bad format index\");\n");
    if ret != "void" {
        let _ = writeln!(s, "    return ({ret}){{0}};");
    }
    s.push_str("}\n\n");
    s
}
