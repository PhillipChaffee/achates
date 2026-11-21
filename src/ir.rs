//! The intermediate representation: one C translation unit as clang
//! understood it, with every implicit conversion explicit and every
//! construct Achates does not represent marked in place.

use std::collections::BTreeMap;

use crate::clang::Loc;
use crate::target::Target;
use crate::types::{IntType, QualType, RecordKind, TagName};

/// A construct Achates does not represent, standing where it occurred.
#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq)]
pub(crate) struct Unsupported {
    pub(crate) clang_kind: String,
    pub(crate) reason: String,
    pub(crate) loc: Option<Loc>,
}

#[derive(Debug)]
pub(crate) struct TranslationUnit {
    pub(crate) file: String,
    pub(crate) target: Target,
    pub(crate) functions: Vec<Function>,
    /// Records reachable from the functions' types.
    pub(crate) records: BTreeMap<(RecordKind, TagName), RecordDef>,
    pub(crate) enums: BTreeMap<TagName, EnumDef>,
    /// File-scope variables the functions refer to.
    pub(crate) globals: BTreeMap<String, Global>,
}

#[derive(serde::Serialize, Debug, Clone)]
pub(crate) struct RecordDef {
    pub(crate) kind: RecordKind,
    pub(crate) name: TagName,
    /// `None` for a record declared but never defined in this unit.
    pub(crate) fields: Option<Vec<Field>>,
    /// Attributes on the definition, such as `packed`; offsets are not kept.
    pub(crate) attrs: Vec<String>,
}

#[derive(serde::Serialize, Debug, Clone)]
pub(crate) struct Field {
    /// Empty for an anonymous struct or union member.
    pub(crate) name: String,
    pub(crate) ty: QualType,
    pub(crate) bit_width: Option<u64>,
}

#[derive(serde::Serialize, Debug, Clone)]
pub(crate) struct EnumDef {
    pub(crate) name: TagName,
    /// The compatible integer type, as clang chose it; `Err` says why it is
    /// unknown.
    pub(crate) underlying: Result<IntType, String>,
    pub(crate) constants: Vec<(String, i128)>,
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Storage {
    None,
    Static,
    Extern,
    Register,
}

#[derive(serde::Serialize, Debug)]
pub(crate) struct Global {
    pub(crate) name: String,
    pub(crate) ty: QualType,
    pub(crate) storage: Storage,
    /// Initializer, when this unit gives one.
    pub(crate) init: Option<Expr>,
    pub(crate) in_main_file: bool,
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Linkage {
    External,
    Internal,
}

/// Where a function is defined, which tells a back end whether to
/// translate it or to model it.
#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Origin {
    MainFile,
    /// A header clang does not treat as a system header.
    ProjectHeader,
    /// A header clang treats as a system header (`/usr/include`, ...).
    SystemHeader,
}

#[derive(serde::Serialize, Debug)]
pub(crate) struct Function {
    pub(crate) name: String,
    pub(crate) origin: Origin,
    /// Absolute path of the file holding the definition; with the name, the
    /// function's identity across translation units.
    pub(crate) def_file: String,
    pub(crate) linkage: Linkage,
    pub(crate) inline: bool,
    pub(crate) params: Vec<Param>,
    pub(crate) ret: QualType,
    pub(crate) variadic: bool,
    pub(crate) noreturn: bool,
    /// Attributes on the definition (`format`, `nonnull`, ...).
    pub(crate) attrs: Vec<String>,
    pub(crate) body: Stmt,
    /// File-scope variables the body names.
    pub(crate) globals: Vec<String>,
    pub(crate) loc: Option<Loc>,
    pub(crate) lines: u64,
}

#[derive(serde::Serialize, Debug, Clone)]
pub(crate) struct Param {
    pub(crate) name: String,
    pub(crate) ty: QualType,
}

/// A variable: parameters by position, locals by a number unique within the
/// function, so shadowing never confuses two variables.
#[derive(serde::Serialize, Debug, Clone, PartialEq, Eq)]
pub(crate) enum VarRef {
    Param { index: usize, name: String },
    Local { id: u32, name: String },
    Global { name: String },
}

#[derive(serde::Serialize, Debug)]
pub(crate) struct LocalVar {
    pub(crate) id: u32,
    pub(crate) name: String,
    pub(crate) ty: QualType,
    pub(crate) storage: Storage,
    pub(crate) init: Option<Expr>,
    pub(crate) attrs: Vec<String>,
}

#[derive(serde::Serialize, Debug)]
pub(crate) enum Decl {
    Var(Box<LocalVar>),
    Unsupported(Unsupported),
}

#[derive(serde::Serialize, Debug)]
pub(crate) enum Stmt {
    Compound(Vec<Self>),
    Decl(Vec<Decl>),
    Expr(Expr),
    If {
        cond: Expr,
        then: Box<Self>,
        els: Option<Box<Self>>,
    },
    While {
        cond: Expr,
        body: Box<Self>,
    },
    DoWhile {
        body: Box<Self>,
        cond: Expr,
    },
    For {
        init: Option<Box<Self>>,
        cond: Option<Box<Expr>>,
        inc: Option<Box<Expr>>,
        body: Box<Self>,
    },
    /// The body holds `Case` and `Default` labels where they were written,
    /// so falling from one case into the next is preserved.
    Switch {
        cond: Expr,
        body: Box<Self>,
    },
    /// `value` is the label's value when clang states it; otherwise the
    /// expression is the integer constant expression as written.
    Case {
        expr: Expr,
        value: Option<i128>,
        body: Box<Self>,
    },
    Default {
        body: Box<Self>,
    },
    Break,
    Continue,
    Return(Option<Expr>),
    Goto(String),
    Label {
        name: String,
        body: Box<Self>,
    },
    Null,
    Unsupported(Unsupported),
}

#[derive(serde::Serialize, Debug)]
pub(crate) struct Expr {
    pub(crate) kind: ExprKind,
    pub(crate) ty: QualType,
    pub(crate) lvalue: bool,
    pub(crate) loc: Option<Loc>,
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnaryOp {
    Plus,
    Minus,
    BitNot,
    Not,
    Deref,
    AddrOf,
    PreInc,
    PreDec,
    PostInc,
    PostDec,
    /// GNU `__extension__`: the value of the operand, with pedantic
    /// warnings silenced.
    Extension,
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinOp {
    Mul,
    Div,
    Rem,
    Add,
    Sub,
    Shl,
    Shr,
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Ne,
    BitAnd,
    BitXor,
    BitOr,
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LogicalOp {
    And,
    Or,
}

/// The conversions clang names, implicit or written as casts.
#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CastKind {
    LValueToRValue,
    NoOp,
    BitCast,
    IntegralCast,
    IntegralToBoolean,
    IntegralToFloating,
    IntegralToPointer,
    FloatingToIntegral,
    FloatingToBoolean,
    FloatingCast,
    PointerToIntegral,
    PointerToBoolean,
    NullToPointer,
    ArrayToPointerDecay,
    FunctionToPointerDecay,
    BuiltinFnToFnPtr,
    ToVoid,
    NonAtomicToAtomic,
    AtomicToNonAtomic,
}

impl CastKind {
    pub(crate) fn from_clang(s: &str) -> Option<Self> {
        Some(match s {
            "LValueToRValue" => Self::LValueToRValue,
            "NoOp" => Self::NoOp,
            "BitCast" => Self::BitCast,
            "IntegralCast" => Self::IntegralCast,
            "IntegralToBoolean" => Self::IntegralToBoolean,
            "IntegralToFloating" => Self::IntegralToFloating,
            "IntegralToPointer" => Self::IntegralToPointer,
            "FloatingToIntegral" => Self::FloatingToIntegral,
            "FloatingToBoolean" => Self::FloatingToBoolean,
            "FloatingCast" => Self::FloatingCast,
            "PointerToIntegral" => Self::PointerToIntegral,
            "PointerToBoolean" => Self::PointerToBoolean,
            "NullToPointer" => Self::NullToPointer,
            "ArrayToPointerDecay" => Self::ArrayToPointerDecay,
            "FunctionToPointerDecay" => Self::FunctionToPointerDecay,
            "BuiltinFnToFnPtr" => Self::BuiltinFnToFnPtr,
            "ToVoid" => Self::ToVoid,
            "NonAtomicToAtomic" => Self::NonAtomicToAtomic,
            "AtomicToNonAtomic" => Self::AtomicToNonAtomic,
            _ => return None,
        })
    }
}

#[derive(serde::Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TypeTrait {
    /// `sizeof`.
    Size,
    /// C11 `_Alignof`.
    Align,
    /// GNU `__alignof__`, the preferred alignment.
    PreferredAlign,
}

#[derive(serde::Serialize, Debug)]
pub(crate) enum TraitArg {
    Type(QualType),
    /// Never evaluated; kept so a reader can see what was measured.
    Expr(Box<Expr>),
}

#[derive(serde::Serialize, Debug)]
pub(crate) enum ExprKind {
    IntLit(u128),
    /// clang's decimal rendering and the IEEE bits Rust reads from it.
    FloatLit {
        text: String,
        bits: u64,
    },
    CharLit(i64),
    /// The bytes written, without the terminating NUL. The type gives the
    /// array length; bytes past the written ones are zero.
    StringLit(Vec<u8>),
    Var(VarRef),
    Func {
        name: String,
        builtin: bool,
    },
    EnumConst {
        name: String,
        value: i128,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// `rhs` is evaluated only if `lhs` does not decide the result.
    Logical {
        op: LogicalOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Comma {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Assign {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// `lhs op= rhs`: `lhs` is converted to `compute_lhs`, combined with
    /// `rhs` in `compute_result`, and converted back to the type of `lhs`.
    CompoundAssign {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        compute_lhs: QualType,
        compute_result: QualType,
    },
    Cond {
        cond: Box<Expr>,
        then: Box<Expr>,
        els: Box<Expr>,
    },
    /// `direct` names the callee when it is a function designator.
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
        direct: Option<String>,
    },
    Member {
        base: Box<Expr>,
        field: String,
        arrow: bool,
    },
    /// `*(lhs + rhs)`, operands in source order.
    Index {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Cast {
        kind: CastKind,
        explicit: bool,
        operand: Box<Expr>,
    },
    TypeTrait {
        trait_: TypeTrait,
        arg: TraitArg,
        value: u64,
    },
    /// `union_field` names the member a union initializer sets; `filler`
    /// initializes array elements past the listed ones.
    InitList {
        elems: Vec<Expr>,
        filler: Option<Box<Expr>>,
        union_field: Option<String>,
    },
    CompoundLiteral(Box<Expr>),
    /// Zero-initialization of an omitted member or element.
    ImplicitValueInit,
    /// `__func__` and its relatives, with the string clang gave them.
    Predefined {
        name: String,
        value: Box<Expr>,
    },
    /// A clang atomic builtin, operands in clang's storage order: pointer,
    /// memory order, then whichever of value, failure order, second value
    /// and weak flag the operation takes.
    Atomic {
        op: String,
        operands: Vec<Expr>,
    },
    Unsupported(Unsupported),
}
