//! Which C values the check can make and look at.
//!
//! A [`Shape`] says how one value is generated, passed, and reported after
//! the call. A function is checkable when every parameter and its result
//! have a shape; otherwise the reason says which type stood in the way.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use crate::check::format;
use crate::emit::Analysis;
use crate::emit::layout::Layouts;
use crate::emit::order::for_each_expr;
use crate::ir::{BinOp, CastKind, Expr, ExprKind, Function, TranslationUnit, UnaryOp, VarRef};
use crate::types::{FloatKind, IntKind, IntType, QualType, RecordKind, TagName, Type, to_c};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Field {
    pub(crate) name: String,
    pub(crate) offset: u64,
    pub(crate) size: u64,
    pub(crate) shape: Shape,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Shape {
    Bool,
    Int {
        ty: IntType,
        c_type: String,
    },
    Float(FloatKind),
    /// mpv's `struct bstr` by value: a pointer to bytes and their number.
    Bstr,
    /// A pointer to a NUL-terminated string.
    CStr,
    /// A `void *` that is only ever handed to talloc as a parent.
    TallocCtx,
    /// A pointer passed as null and reported by where it points afterwards.
    Slot {
        c_type: String,
    },
    /// A struct whose members are scalars, arrays of scalars, `bstr`s or
    /// structs of the same kind.
    Struct {
        c_type: String,
        size: u64,
        align: u64,
        fields: Vec<Field>,
    },
    /// A fixed-length array member.
    Array {
        elem: Box<Self>,
        len: u64,
        elem_size: u64,
    },
    /// A pointer to one object, or null: the object is generated before the
    /// call and reported after it.
    Ptr {
        pointee: Box<Self>,
        size: u64,
        align: u64,
    },
    /// The format of a function whose `...` or `va_list` reaches
    /// `vsnprintf` or `vsscanf`: one of that kind's formats, followed by
    /// the arguments it asks for.
    Format(format::Kind),
    /// A `va_list` holding the arguments the preceding format asks for.
    VaList,
    /// A null-terminated array of C strings that the function only reads
    /// (`char **langs`, walked until `langs[i]` is null).
    StrList {
        c_type: String,
    },
}

impl Shape {
    /// The C type of a variable holding the value.
    pub(crate) fn c_type(&self) -> String {
        match self {
            Self::Bool => "_Bool".into(),
            Self::Int { c_type, .. }
            | Self::Slot { c_type }
            | Self::Struct { c_type, .. }
            | Self::StrList { c_type } => c_type.clone(),
            Self::Float(FloatKind::Float) => "float".into(),
            Self::Float(FloatKind::Double) => "double".into(),
            Self::Bstr => "struct bstr".into(),
            Self::CStr => "char *".into(),
            Self::TallocCtx => "void *".into(),
            // Only a struct member is an array, and members are assigned one by one.
            Self::Array { elem, .. } => elem.c_type(),
            Self::Ptr { pointee, .. } => format!("{} *", pointee.c_type()),
            Self::Format(_) => "const char *".into(),
            Self::VaList => "va_list".into(),
        }
    }

    pub(crate) fn any(&self, f: &dyn Fn(&Self) -> bool) -> bool {
        f(self)
            || match self {
                Self::Struct { fields, .. } => fields.iter().any(|x| x.shape.any(f)),
                Self::Array { elem, .. } => elem.any(f),
                Self::Ptr { pointee, .. } => pointee.any(f),
                _ => false,
            }
    }
}

/// How a function is called by the check.
#[derive(Debug, Clone)]
pub(crate) struct Plan {
    pub(crate) params: Vec<(String, Shape)>,
    /// `None` for `void`.
    pub(crate) ret: Option<Shape>,
    /// The function is variadic: its `...` gets the arguments its format
    /// (the last parameter, a `Shape::Format`) asks for.
    pub(crate) variadic: bool,
}

impl Plan {
    pub(crate) fn any(&self, f: &dyn Fn(&Shape) -> bool) -> bool {
        self.params.iter().any(|p| p.1.any(f)) || self.ret.as_ref().is_some_and(|r| r.any(f))
    }
}

/// How a function body uses one pointer parameter.
#[derive(Debug, Default)]
struct Uses {
    total: usize,
    /// Passed as an argument: the callee and the position.
    args: Vec<(Option<String>, usize)>,
    reads: usize,
    writes: usize,
    members: usize,
    null_tests: usize,
    arithmetic: usize,
}

impl Uses {
    fn other(&self) -> usize {
        self.total.saturating_sub(
            self.args.len()
                + self.reads
                + self.writes
                + self.members
                + self.null_tests
                + self.arithmetic,
        )
    }
}

fn strip(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Cast {
            kind: CastKind::LValueToRValue | CastKind::NoOp | CastKind::BitCast,
            operand,
            ..
        } => strip(operand),
        _ => e,
    }
}

fn is_param(e: &Expr, index: usize) -> bool {
    matches!(&strip(e).kind, ExprKind::Var(VarRef::Param { index: i, .. }) if *i == index)
}

fn uses(f: &Function, index: usize) -> Uses {
    let mut u = Uses::default();
    // The left sides of assignments, by identity: a dereference there is a
    // write, anywhere else a read.
    let mut targets: HashSet<*const Expr> = HashSet::new();
    for_each_expr(&f.body, &mut |e| {
        if let ExprKind::Assign { lhs, .. } = &e.kind {
            targets.insert(std::ptr::from_ref::<Expr>(lhs));
        }
    });
    for_each_expr(&f.body, &mut |e| {
        let here = std::ptr::from_ref::<Expr>(e);
        let mut deref = || {
            if targets.contains(&here) {
                u.writes += 1;
            } else {
                u.reads += 1;
            }
        };
        match &e.kind {
            ExprKind::Var(VarRef::Param { index: i, .. }) if *i == index => u.total += 1,
            ExprKind::Call { args, direct, .. } => {
                for (pos, a) in args.iter().enumerate() {
                    if is_param(a, index) {
                        u.args.push((direct.clone(), pos));
                    }
                }
            }
            ExprKind::Unary {
                op: UnaryOp::Deref,
                operand,
            } if is_param(operand, index) => deref(),
            ExprKind::Index { lhs, rhs } if is_param(lhs, index) => {
                if matches!(rhs.kind, ExprKind::IntLit(0)) {
                    deref();
                } else {
                    u.arithmetic += 1;
                }
            }
            ExprKind::Member {
                base, arrow: true, ..
            } if is_param(base, index) => u.members += 1,
            ExprKind::Cast {
                kind: CastKind::PointerToBoolean,
                operand,
                ..
            } if is_param(operand, index) => u.null_tests += 1,
            ExprKind::Unary {
                op: UnaryOp::Not,
                operand,
            } if is_param(operand, index) => u.null_tests += 1,
            // `p && ...`: clang gives a logical operand no conversion node.
            ExprKind::Logical { lhs, rhs, .. } => {
                u.null_tests +=
                    usize::from(is_param(lhs, index)) + usize::from(is_param(rhs, index));
            }
            ExprKind::Binary {
                op: BinOp::Eq | BinOp::Ne,
                lhs,
                rhs,
            } if is_param(lhs, index) || is_param(rhs, index) => u.null_tests += 1,
            ExprKind::Binary {
                op: BinOp::Add | BinOp::Sub,
                lhs,
                rhs,
            } if is_param(lhs, index) || is_param(rhs, index) => u.arithmetic += 1,
            ExprKind::Unary {
                op: UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec,
                operand,
            } if is_param(operand, index) => u.arithmetic += 1,
            ExprKind::CompoundAssign { lhs, .. } if is_param(lhs, index) => u.arithmetic += 1,
            _ => {}
        }
    });
    u
}

/// Functions outside the selection whose argument at the given position is
/// a talloc parent.
const TALLOC_PARENTS: &[(&str, usize)] = &[
    ("ta_alloc_size", 0),
    ("ta_zalloc_size", 0),
    ("ta_new_context", 0),
    ("ta_realloc_size", 0),
    ("ta_xrealloc_size", 0),
    ("ta_steal_", 0),
    ("ta_set_parent", 1),
    ("ta_xstrdup", 0),
    ("ta_xstrndup", 0),
    ("ta_strdup", 0),
    ("ta_strndup", 0),
    ("ta_asprintf", 0),
    ("ta_xmemdup", 0),
];

pub(crate) struct Shapes<'a> {
    a: &'a Analysis,
    /// `(function key, parameter)` pairs found to be talloc parents.
    talloc: BTreeSet<(String, usize)>,
}

fn is_void_ptr(t: &QualType) -> bool {
    matches!(&t.ty, Type::Pointer(p) if matches!(p.ty, Type::Void))
}

fn unqualified(t: &QualType) -> QualType {
    QualType::plain(t.ty.clone())
}

impl<'a> Shapes<'a> {
    pub(crate) fn new(a: &'a Analysis) -> Self {
        // Greatest fixed point: start from every `void *` parameter and drop
        // those with a use that is not a hand-over to a talloc parent.
        let mut talloc: BTreeSet<(String, usize)> = BTreeSet::new();
        let mut found: BTreeMap<(String, usize), Uses> = BTreeMap::new();
        for r in &a.rows {
            if let Some((f, _, _)) = a.function(&r.key) {
                for (i, p) in f.params.iter().enumerate() {
                    if is_void_ptr(&p.ty) {
                        talloc.insert((r.key.clone(), i));
                        found.insert((r.key.clone(), i), uses(f, i));
                    }
                }
            }
        }
        loop {
            let keep: BTreeSet<(String, usize)> = talloc
                .iter()
                .filter(|(key, i)| {
                    found.get(&(key.clone(), *i)).is_some_and(|u| {
                        !u.args.is_empty()
                            && u.total == u.args.len()
                            && u.args.iter().all(|(callee, pos)| {
                                callee.as_ref().is_some_and(|c| {
                                    TALLOC_PARENTS.contains(&(c.as_str(), *pos))
                                        || a.resolve(key, c)
                                            .is_some_and(|k| talloc.contains(&(k, *pos)))
                                })
                            })
                    })
                })
                .cloned()
                .collect();
            if keep.len() == talloc.len() {
                break;
            }
            talloc = keep;
        }
        Self { a, talloc }
    }

    fn int(tu: &TranslationUnit, lay: &Layouts, t: &QualType) -> Option<Shape> {
        let c_type = to_c(&unqualified(t))?;
        match &t.ty {
            Type::Int(i) => Some(Shape::Int { ty: *i, c_type }),
            Type::Enum(n) => {
                let ty = lay
                    .enums
                    .get(n)
                    .copied()
                    .or_else(|| tu.enums.get(n).and_then(|e| e.underlying.clone().ok()))?;
                Some(Shape::Int { ty, c_type })
            }
            _ => None,
        }
    }

    /// A value held directly: a scalar, a `bstr`, or a struct of such.
    fn value(tu: &TranslationUnit, lay: &Layouts, t: &QualType) -> Result<Shape, String> {
        match &t.ty {
            Type::Bool { .. } => Ok(Shape::Bool),
            Type::Int(_) | Type::Enum(_) => {
                Self::int(tu, lay, t).ok_or_else(|| format!("{t}: no C name or no integer type"))
            }
            Type::Float { kind, .. } => Ok(Shape::Float(*kind)),
            Type::Record { kind, name } => Self::record(tu, lay, t, *kind, name),
            Type::Array {
                elem,
                len: Some(len),
            } => {
                let shape = Self::value(tu, lay, elem)?;
                if !matches!(shape, Shape::Bool | Shape::Int { .. } | Shape::Float(_)) {
                    return Err(format!("{t}: an array whose elements are not scalars"));
                }
                let (elem_size, _) = lay.size_align(elem)?;
                Ok(Shape::Array {
                    elem: Box::new(shape),
                    len: *len,
                    elem_size,
                })
            }
            Type::Pointer(_) => Err("a pointer member".into()),
            Type::Atomic(_) => Err("an atomic member".into()),
            _ => Err(format!("{t}")),
        }
    }

    fn is_bstr(tu: &TranslationUnit, kind: RecordKind, name: &TagName) -> bool {
        let Some(def) = tu.records.get(&(kind, name.clone())) else {
            return false;
        };
        let Some(fields) = &def.fields else {
            return false;
        };
        kind == RecordKind::Struct
            && *name == TagName::Tag("bstr".into())
            && matches!(fields.as_slice(), [start, len]
                if start.name == "start" && len.name == "len"
                    && matches!(&start.ty.ty, Type::Pointer(p)
                        if matches!(p.ty, Type::Int(IntType { bits: 8, .. })))
                    && matches!(len.ty.ty, Type::Int(IntType { bits: 64, signed: false, .. })))
    }

    fn record(
        tu: &TranslationUnit,
        lay: &Layouts,
        t: &QualType,
        kind: RecordKind,
        name: &TagName,
    ) -> Result<Shape, String> {
        let what = format!("{} {name}", kind.keyword());
        if Self::is_bstr(tu, kind, name) {
            return Ok(Shape::Bstr);
        }
        if kind == RecordKind::Union {
            return Err(format!("{what}: a union"));
        }
        let key = (kind, name.clone());
        let def = tu
            .records
            .get(&key)
            .ok_or_else(|| format!("{what}: no definition"))?;
        let fields = def
            .fields
            .as_ref()
            .ok_or_else(|| format!("{what}: declared but not defined in this file"))?;
        let l = lay
            .records
            .get(&key)
            .ok_or_else(|| format!("{what}: no layout"))?;
        let (size, align) = lay.size_align(t)?;
        let c_type = to_c(&unqualified(t)).ok_or_else(|| format!("{what}: no C name"))?;
        let mut out = Vec::new();
        for (i, f) in fields.iter().enumerate() {
            if f.name.is_empty() || f.bit_width.is_some() {
                return Err(format!("{what}: has an anonymous member or a bit-field"));
            }
            let offset = l
                .offsets
                .get(i)
                .cloned()
                .unwrap_or_else(|| Err("no offset".into()))
                .map_err(|e| format!("{what}.{}: {e}", f.name))?;
            let shape = Self::value(tu, lay, &f.ty)
                .map_err(|e| format!("{what}: member `{}` is {e}", f.name))?;
            let (fsize, _) = lay.size_align(&f.ty)?;
            out.push(Field {
                name: f.name.clone(),
                offset,
                size: fsize,
                shape,
            });
        }
        Ok(Shape::Struct {
            c_type,
            size,
            align,
            fields: out,
        })
    }

    fn param(&self, key: &str, f: &Function, index: usize, t: &QualType) -> Result<Shape, String> {
        let (_, tu, lay) = self.a.function(key).ok_or("no IR")?;
        let Type::Pointer(p) = &t.ty else {
            return Self::value(tu, lay, t);
        };
        if crate::emit::expr::is_va_tag(p) {
            return Ok(Shape::VaList);
        }
        let u = uses(f, index);
        match &p.ty {
            Type::Int(IntType {
                kind: IntKind::Char,
                ..
            }) => Ok(Shape::CStr),
            Type::Int(IntType { bits: 8, .. }) => {
                Err(format!("{t}: a pointer to bytes without an evident length"))
            }
            Type::Void => {
                if self.talloc.contains(&(key.to_owned(), index)) {
                    Ok(Shape::TallocCtx)
                } else {
                    Err("a `void *` that is not only handed to talloc as a parent".into())
                }
            }
            Type::Function(_) => Err("a function pointer".into()),
            Type::Pointer(inner)
                if matches!(
                    inner.ty,
                    Type::Int(IntType {
                        kind: IntKind::Char,
                        ..
                    })
                ) && u.writes == 0
                    && u.args.is_empty()
                    && u.other() == 0
                    && u.reads + u.arithmetic > 0 =>
            {
                let c_type = to_c(t).ok_or("no C name")?;
                Ok(Shape::StrList { c_type })
            }
            Type::Pointer(_) => {
                if u.reads == 0 && u.arithmetic == 0 && u.args.is_empty() && u.other() == 0 {
                    let c_type = to_c(&unqualified(p)).ok_or("no C name")?;
                    Ok(Shape::Ptr {
                        pointee: Box::new(Shape::Slot { c_type }),
                        size: 8,
                        align: 8,
                    })
                } else {
                    Err(format!(
                        "{t}: a pointer to a pointer that the function reads or passes on"
                    ))
                }
            }
            _ => {
                let pointee = Self::value(tu, lay, p).map_err(|e| format!("a pointer to {e}"))?;
                let scalar = matches!(pointee, Shape::Bool | Shape::Int { .. } | Shape::Float(_));
                if u.arithmetic > 0 || (scalar && u.other() > 0) {
                    return Err(format!(
                        "{t}: a pointer used as an array without an evident length"
                    ));
                }
                let (size, align) = lay.size_align(p)?;
                Ok(Shape::Ptr {
                    pointee: Box::new(pointee),
                    size,
                    align,
                })
            }
        }
    }

    fn result(&self, key: &str, t: &QualType) -> Result<Option<Shape>, String> {
        let (_, tu, lay) = self.a.function(key).ok_or("no IR")?;
        match &t.ty {
            Type::Void => Ok(None),
            Type::Pointer(p) => Ok(Some(match &p.ty {
                Type::Int(IntType {
                    kind: IntKind::Char,
                    ..
                }) => Shape::CStr,
                Type::Function(_) => return Err("a function pointer".into()),
                _ => Shape::Slot {
                    c_type: to_c(&unqualified(t)).ok_or("no C name")?,
                },
            })),
            _ => Self::value(tu, lay, t).map(Some),
        }
    }

    /// Gives the format parameter of a function with `...` or a `va_list`
    /// parameter its shape: the `const char *` just before them, when what
    /// the arguments reach is `vsnprintf`.
    fn formats(
        &self,
        key: &str,
        f: &Function,
        params: &mut [(String, Shape)],
    ) -> Result<(), String> {
        let lists: Vec<usize> = params
            .iter()
            .enumerate()
            .filter(|(_, (_, s))| *s == Shape::VaList)
            .map(|(i, _)| i)
            .collect();
        let fmt = match (f.variadic, lists.as_slice()) {
            (false, []) => return Ok(()),
            (true, []) => params.len().checked_sub(1),
            (false, [i]) if *i + 1 == params.len() => i.checked_sub(1),
            _ => None,
        };
        let exts = self
            .a
            .rows
            .iter()
            .find(|r| r.key == key)
            .map(|r| &r.res.exts);
        let kind = match exts.map(|e| (e.contains("vsnprintf"), e.contains("vsscanf"))) {
            Some((true, false)) => Some(format::Kind::Printf),
            Some((false, true)) => Some(format::Kind::Scanf),
            _ => None,
        };
        match (fmt.and_then(|i| params.get_mut(i)), kind) {
            (Some((_, s)), Some(k)) if *s == Shape::CStr => {
                *s = Shape::Format(k);
                Ok(())
            }
            _ => Err(
                "variadic arguments: the check makes them only for a format just before `...` or a `va_list` that reaches vsnprintf or vsscanf".into(),
            ),
        }
    }

    /// The plan for one function, or why it has none.
    pub(crate) fn plan(&self, key: &str) -> Result<Plan, Vec<String>> {
        let Some((f, _, _)) = self.a.function(key) else {
            return Err(vec!["no IR".into()]);
        };
        let mut reasons = Vec::new();
        let mut params = Vec::new();
        for (i, p) in f.params.iter().enumerate() {
            match self.param(key, f, i, &p.ty) {
                Ok(s) => params.push((p.name.clone(), s)),
                Err(e) => reasons.push(format!("parameter type: {e}")),
            }
        }
        let ret = match self.result(key, &f.ret) {
            Ok(r) => r,
            Err(e) => {
                reasons.push(format!("result type: {e}"));
                None
            }
        };
        if let Err(e) = self.formats(key, f, &mut params) {
            reasons.push(e);
        }
        if reasons.is_empty() {
            Ok(Plan {
                params,
                ret,
                variadic: f.variadic,
            })
        } else {
            reasons.sort();
            reasons.dedup();
            Err(reasons)
        }
    }
}
