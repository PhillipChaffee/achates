//! Expressions: each C expression becomes the statements that compute it,
//! in source order, and one Lean term for its value.
//!
//! Every operation that can fail or touches memory gets a line of its own,
//! so the order of effects is the order of the lines. Terms returned here
//! are atomic: a name, or something in parentheses.

use crate::emit::func::{FnEmitter, VarInfo};
use crate::emit::names::{self, Sig, float_ty, int_ns, int_ty};
use crate::emit::order::var_key;
use crate::emit::world::{ATOMIC, SIGNED_ZERO, Target};
use crate::ir::{BinOp, CastKind, Expr, ExprKind, LogicalOp, UnaryOp, VarRef};
use crate::types::{FloatKind, FnType, IntType, QualType, RecordKind, TagName, Type};

/// A C type as the emitter treats it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum K {
    Void,
    Bool,
    Int(IntType),
    Float(FloatKind),
    Ptr,
    Agg,
    Bad,
}

pub(crate) enum Lv {
    Temp(String),
    /// An address term and a constant offset still to be added to it.
    Mem(String, u64),
}

impl FnEmitter<'_> {
    pub(crate) fn kind(&mut self, t: &QualType) -> K {
        match &t.ty {
            Type::Void => K::Void,
            Type::Bool { .. } => K::Bool,
            Type::Int(i) => K::Int(*i),
            Type::Float { kind, .. } => K::Float(*kind),
            Type::Pointer(_) => K::Ptr,
            Type::Array { .. } | Type::Record { .. } => K::Agg,
            Type::Enum(n) => match self.u.tu.enums.get(n).map(|e| e.underlying.clone()) {
                Some(Ok(i)) => K::Int(i),
                _ => {
                    self.refuse(format!("enum {n} without a known integer type"));
                    K::Bad
                }
            },
            Type::Atomic(inner) => {
                self.res.assumptions.insert(ATOMIC.to_owned());
                self.kind(inner)
            }
            Type::Function(_) | Type::Unsupported { .. } => {
                self.refuse(format!("type {t} has no Lean counterpart"));
                K::Bad
            }
        }
    }

    pub(crate) fn lty(&mut self, t: &QualType) -> String {
        match self.kind(t) {
            K::Void | K::Bad => "Unit".into(),
            K::Bool => "Bool".into(),
            K::Int(i) => int_ty(i),
            K::Float(k) => float_ty(k).into(),
            K::Ptr => "Ptr".into(),
            K::Agg => "Agg".into(),
        }
    }

    pub(crate) fn size_align(&mut self, t: &QualType) -> Option<(u64, u64)> {
        let t = match &t.ty {
            Type::Enum(_) => match self.kind(t) {
                K::Int(i) => QualType::plain(Type::Int(i)),
                _ => return None,
            },
            _ => t.clone(),
        };
        match self.u.lay.size_align(&t) {
            Ok(x) => Some(x),
            Err(e) => {
                self.refuse(format!("layout: {e}"));
                None
            }
        }
    }

    /// Size of the type a pointer or array type refers to; `void` counts
    /// as one byte, the GNU rule the build relies on.
    fn elem_size(&mut self, t: &QualType) -> u64 {
        match &t.ty {
            Type::Pointer(p) if matches!(p.ty, Type::Void) => 1,
            Type::Pointer(p) | Type::Array { elem: p, .. } => self.size_align(p).map_or(1, |x| x.0),
            _ => {
                self.refuse("pointer arithmetic on a non-pointer");
                1
            }
        }
    }

    pub(crate) fn lit(&mut self, v: i128, i: IntType) -> String {
        let (lo, hi) = if i.signed {
            (-(1i128 << (i.bits - 1).min(126)), (1i128 << (i.bits - 1).min(126)) - 1)
        } else {
            (0, if i.bits >= 127 { i128::MAX } else { (1i128 << i.bits) - 1 })
        };
        if v < lo || v > hi {
            return self.refuse(format!("constant {v} outside its type"));
        }
        if v >= 0 {
            format!("({v} : {})", int_ty(i))
        } else {
            format!("(SInt.ofInt {} ({v}))", i.bits)
        }
    }

    fn at(&mut self, ptr: &str, off: u64) -> String {
        if off == 0 {
            ptr.to_owned()
        } else {
            self.bind("Ptr", &format!("Ptr.add {ptr} 1 {off}"))
        }
    }

    fn addr(&mut self, lv: Lv) -> String {
        match lv {
            Lv::Mem(p, off) => self.at(&p, off),
            Lv::Temp(_) => self.refuse("address of a variable held as a value (Achates bug)"),
        }
    }

    fn load(&mut self, lv: Lv, t: &QualType) -> String {
        let ptr = match lv {
            Lv::Temp(name) => return name,
            Lv::Mem(p, off) => self.at(&p, off),
        };
        let ty = self.lty(t);
        match self.kind(t) {
            K::Agg => match self.size_align(t) {
                Some((s, a)) => self.bind("Agg", &format!("Mem.loadAgg {ptr} {s} {a}")),
                None => "default".into(),
            },
            K::Void | K::Bad => self.refuse("load of a value without a type"),
            _ => self.bind(&ty, &format!("Mem.load {ty} {ptr}")),
        }
    }

    pub(crate) fn store_to(&mut self, ptr: &str, off: u64, t: &QualType, v: &str) {
        let p = self.at(ptr, off);
        match self.kind(t) {
            K::Agg => {
                if let Some((_, a)) = self.size_align(t) {
                    self.line(format!("Mem.storeAgg {p} {v} {a}"));
                }
            }
            K::Void | K::Bad => {
                self.refuse("store of a value without a type");
            }
            _ => self.line(format!("Mem.store {p} {v}")),
        }
    }

    fn store_lv(&mut self, lv: Lv, t: &QualType, v: &str) {
        match lv {
            Lv::Temp(name) => self.line(format!("{name} := {v}")),
            Lv::Mem(p, off) => self.store_to(&p, off, t, v),
        }
    }

    fn record_of(&mut self, t: &QualType) -> Option<(RecordKind, TagName)> {
        match &t.ty {
            Type::Record { kind, name } => Some((*kind, name.clone())),
            Type::Atomic(inner) => self.record_of(inner),
            _ => {
                self.refuse(format!("member access on {t}"));
                None
            }
        }
    }

    /// Offset of a member, as clang laid the record out.
    fn field_offset(&mut self, rec: &QualType, field: &str, fty: &QualType) -> u64 {
        let Some(key) = self.record_of(rec) else { return 0 };
        let pos = self.u.tu.records.get(&key).and_then(|d| {
            d.fields.as_ref()?.iter().position(|f| {
                // An anonymous member has no name; its type identifies it.
                f.name == field && (!field.is_empty() || f.ty.ty == fty.ty)
            })
        });
        let off = pos.and_then(|i| self.u.lay.records.get(&key)?.offsets.get(i).cloned());
        match off {
            Some(Ok(o)) => o,
            Some(Err(e)) => {
                self.refuse(format!("member `{field}` of {rec}: {e}"));
                0
            }
            None => {
                self.refuse(format!("member `{field}` of {rec}: no layout from clang"));
                0
            }
        }
    }

    fn var_lv(&mut self, v: &VarRef) -> Lv {
        if let Some(info) = var_key(v).and_then(|k| self.vars.get(&k)) {
            return match info {
                VarInfo::Temp(n) => Lv::Temp(n.clone()),
                VarInfo::Mem(p) => Lv::Mem(p.clone(), 0),
            };
        }
        let term = match v {
            VarRef::Local { id, .. } => self.statics.get(id).cloned().ok_or_else(|| "local without storage".to_owned()),
            VarRef::Global { name } => match self.u.globals.get(name) {
                None => Err(format!("object `{name}` is defined outside the selection")),
                Some(key) => self.w.statics.term(key).map_err(|e| format!("object `{name}`: {e}")),
            },
            VarRef::Param { name, .. } => Err(format!("parameter `{name}` without storage")),
        };
        match term {
            Ok(t) => Lv::Mem(t, 0),
            Err(e) => Lv::Mem(self.refuse(e), 0),
        }
    }

    fn index_lv(&mut self, e: &Expr, lhs: &Expr, rhs: &Expr) -> Lv {
        let (p, i) = if self.kind(&lhs.ty) == K::Ptr { (lhs, rhs) } else { (rhs, lhs) };
        let pt = self.rv(p);
        let it = self.rv(i);
        let n = self.to_int(&it, &i.ty);
        let size = self.size_align(&e.ty).map_or(1, |x| x.0);
        Lv::Mem(self.bind("Ptr", &format!("Ptr.add {pt} {size} {n}")), 0)
    }

    pub(crate) fn lv(&mut self, e: &Expr) -> Lv {
        match &e.kind {
            ExprKind::Var(v) => self.var_lv(v),
            ExprKind::Member { base, field, arrow } => {
                if *arrow {
                    let Type::Pointer(rec) = &base.ty.ty else {
                        return Lv::Mem(self.refuse("`->` on a non-pointer"), 0);
                    };
                    let off = self.field_offset(rec, field, &e.ty);
                    Lv::Mem(self.rv(base), off)
                } else {
                    let off = self.field_offset(&base.ty, field, &e.ty);
                    match self.lv(base) {
                        Lv::Mem(p, o) => Lv::Mem(p, o + off),
                        Lv::Temp(_) => Lv::Mem(self.refuse("member of a scalar"), 0),
                    }
                }
            }
            ExprKind::Index { lhs, rhs } => self.index_lv(e, lhs, rhs),
            ExprKind::Unary {
                op: UnaryOp::Deref,
                operand,
            } => Lv::Mem(self.rv(operand), 0),
            ExprKind::Unary {
                op: UnaryOp::Extension,
                operand,
            }
            | ExprKind::Cast {
                kind: CastKind::NoOp,
                operand,
                ..
            } => self.lv(operand),
            ExprKind::StringLit(bytes) => {
                let size = self.size_align(&e.ty).map_or(0, |x| x.0);
                Lv::Mem(self.w.statics.string(bytes, size), 0)
            }
            ExprKind::Predefined { value, .. } => self.lv(value),
            ExprKind::CompoundLiteral(init) => self.compound_literal(e, init),
            _ => Lv::Mem(self.refuse("expression used as an object that Achates does not treat as one"), 0),
        }
    }

    fn compound_literal(&mut self, e: &Expr, init: &Expr) -> Lv {
        if self.in_static {
            return Lv::Mem(self.refuse("compound literal in a static initialiser"), 0);
        }
        let name = self.fresh("cl");
        if let Some((size, align)) = self.size_align(&e.ty) {
            self.frame_objs.push((name.clone(), size, align));
            self.line(format!("Mem.undefine {name} {size}"));
        }
        self.init_at(&name, 0, &e.ty, init);
        Lv::Mem(name, 0)
    }

    fn to_int(&mut self, term: &str, t: &QualType) -> String {
        match self.kind(t) {
            K::Int(i) => format!("({}.toInt {term})", int_ns(i)),
            _ => self.refuse("integer expected"),
        }
    }

    fn of_bool(&mut self, c: &str, t: &QualType) -> String {
        match self.kind(t) {
            K::Int(i) => format!("({}.ofBool {} {c})", int_ns(i), i.bits),
            K::Bool => c.to_owned(),
            _ => self.refuse("truth value of a non-integer type"),
        }
    }

    fn float_op(&mut self) {
        for f in &self.u.float_flags {
            if f == "-fno-signed-zeros" {
                self.res.assumptions.insert(SIGNED_ZERO.to_owned());
            } else {
                let r = format!("floating-point arithmetic compiled with {f}");
                if !self.res.reasons.contains(&r) {
                    self.res.reasons.push(r);
                }
            }
        }
    }

    /// Converts between scalar types the way the C conversion does.
    pub(crate) fn convert(&mut self, v: &str, from: &QualType, to: &QualType) -> String {
        let (a, b) = (self.kind(from), self.kind(to));
        match (a, b) {
            _ if a == b => v.to_owned(),
            (K::Int(x), K::Int(y)) => {
                format!("({}.to{} {} {v})", int_ns(x), if y.signed { 'S' } else { 'U' }, y.bits)
            }
            (K::Bool, K::Int(y)) => format!("({}.ofBool {} {v})", int_ns(y), y.bits),
            (K::Int(_) | K::Float(_), K::Bool) => format!("({v} != 0)"),
            (K::Ptr, K::Bool) => format!("({v} != Ptr.null)"),
            (K::Int(x), K::Float(k)) => {
                let f = if x.signed { "ofS" } else { "ofU" };
                self.bind(float_ty(k), &format!("{}.{f} {v}", float_ty(k)))
            }
            (K::Float(k), K::Int(y)) => {
                let f = if y.signed { "toS" } else { "toU" };
                self.bind(&int_ty(y), &format!("{}.{f} {} {v}", float_ty(k), y.bits))
            }
            (K::Float(FloatKind::Float), K::Float(FloatKind::Double)) => format!("(Float32.toFloat {v})"),
            (K::Float(FloatKind::Double), K::Float(FloatKind::Float)) => format!("(Float.toFloat32 {v})"),
            (K::Bool, K::Float(k)) => format!("(if {v} then (1 : {}) else 0)", float_ty(k)),
            _ => self.refuse(format!("conversion from {from} to {to}")),
        }
    }

    fn cast(&mut self, e: &Expr, kind: CastKind, operand: &Expr) -> String {
        match kind {
            CastKind::LValueToRValue => {
                let l = self.lv(operand);
                self.load(l, &e.ty)
            }
            CastKind::NoOp | CastKind::NonAtomicToAtomic | CastKind::AtomicToNonAtomic => self.rv(operand),
            CastKind::BitCast => {
                if self.kind(&operand.ty) != K::Ptr || self.kind(&e.ty) != K::Ptr {
                    return self.refuse("bit cast between non-pointer types");
                }
                self.rv(operand)
            }
            CastKind::IntegralCast
            | CastKind::IntegralToBoolean
            | CastKind::IntegralToFloating
            | CastKind::FloatingToIntegral
            | CastKind::FloatingToBoolean
            | CastKind::FloatingCast
            | CastKind::PointerToBoolean => {
                let v = self.rv(operand);
                self.convert(&v, &operand.ty, &e.ty)
            }
            CastKind::IntegralToPointer => {
                let v = self.rv(operand);
                match self.kind(&operand.ty) {
                    K::Int(i) => format!("(Ptr.ofNat (UInt.toNat ({}.toU 64 {v})))", int_ns(i)),
                    _ => self.refuse("non-integer converted to a pointer"),
                }
            }
            CastKind::PointerToIntegral => {
                let v = self.rv(operand);
                let n = self.bind("Nat", &format!("Ptr.toNat {v}"));
                match self.kind(&e.ty) {
                    K::Int(i) if i.signed => format!("(SInt.ofInt {} {n})", i.bits),
                    K::Int(i) => format!("(UInt.ofNat {} {n})", i.bits),
                    _ => self.refuse("pointer converted to a non-integer"),
                }
            }
            CastKind::NullToPointer => {
                self.effect(operand);
                "Ptr.null".into()
            }
            CastKind::ArrayToPointerDecay => {
                let l = self.lv(operand);
                self.addr(l)
            }
            CastKind::FunctionToPointerDecay | CastKind::BuiltinFnToFnPtr => self.fn_value(operand),
            CastKind::ToVoid => {
                self.effect(operand);
                "()".into()
            }
        }
    }

    /// The address of a function: a pointer that carries the function's key.
    fn fn_value(&mut self, e: &Expr) -> String {
        match &e.kind {
            ExprKind::Func { name, builtin: false } => {
                let id = self.u.fn_key(self.w, name).cloned().unwrap_or_else(|| name.clone());
                let sig = match &e.ty.ty {
                    Type::Function(ft) => self.sig_of(ft),
                    _ => None,
                };
                self.w.addressed.entry(id.clone()).or_insert(sig);
                format!("(Ptr.fn \"{id}\")")
            }
            ExprKind::Unary {
                op: UnaryOp::Deref | UnaryOp::Extension,
                operand,
            } => self.rv(operand),
            _ => self.refuse("function designator Achates does not recognise"),
        }
    }

    pub(crate) fn sig_of(&mut self, ft: &FnType) -> Option<Sig> {
        if !ft.prototyped {
            self.refuse("call through a function type without a prototype");
            return None;
        }
        let params = ft.params.iter().map(|p| self.lty(p)).collect();
        let ret = self.lty(&ft.ret);
        Some(Sig {
            params,
            variadic: ft.variadic,
            ret,
        })
    }

    fn arith(&mut self, op: BinOp, t: &QualType, a: &str, b: &str, bt: &QualType) -> String {
        let name = match op {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::Div => "div",
            BinOp::Rem => "rem",
            BinOp::Shl => "shl",
            BinOp::Shr => "shr",
            BinOp::BitAnd => "band",
            BinOp::BitOr => "bor",
            BinOp::BitXor => "bxor",
            _ => return self.refuse("comparison where arithmetic was expected"),
        };
        let sym = match op {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            _ => "/",
        };
        match self.kind(t) {
            K::Int(i) => {
                let ns = int_ns(i);
                let ty = int_ty(i);
                match op {
                    BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => format!("({ns}.{name} {a} {b})"),
                    BinOp::Shl | BinOp::Shr => {
                        let n = self.to_int(b, bt);
                        self.bind(&ty, &format!("{ns}.{name} {a} {n}"))
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul if !i.signed => format!("({a} {sym} {b})"),
                    _ => self.bind(&ty, &format!("{ns}.{name} {a} {b}")),
                }
            }
            K::Float(_) if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div) => {
                self.float_op();
                format!("({a} {sym} {b})")
            }
            _ => self.refuse(format!("operator on {t}")),
        }
    }

    fn compare(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr) -> String {
        let a = self.rv(lhs);
        let b = self.rv(rhs);
        let (sym, name) = match op {
            BinOp::Lt => ("<", "lt"),
            BinOp::Gt => (">", "gt"),
            BinOp::Le => ("≤", "le"),
            BinOp::Ge => ("≥", "ge"),
            BinOp::Eq => ("==", "eq"),
            _ => ("!=", "ne"),
        };
        match (self.kind(&lhs.ty), self.kind(&rhs.ty)) {
            (K::Ptr, K::Ptr) => self.bind("Bool", &format!("Ptr.{name} {a} {b}")),
            (x, y) if x == y && matches!(x, K::Int(_) | K::Float(_) | K::Bool) => {
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    format!("({a} {sym} {b})")
                } else {
                    format!("(decide ({a} {sym} {b}))")
                }
            }
            _ => self.refuse("comparison of operands of different types"),
        }
    }

    fn pointer_arith(&mut self, e: &Expr, op: BinOp, lhs: &Expr, rhs: &Expr) -> String {
        let (lk, rk) = (self.kind(&lhs.ty), self.kind(&rhs.ty));
        let a = self.rv(lhs);
        let b = self.rv(rhs);
        match (op, lk, rk) {
            (BinOp::Sub, K::Ptr, K::Ptr) => {
                let size = self.elem_size(&lhs.ty);
                let d = self.bind("I64", &format!("Ptr.diff {a} {b} {size}"));
                let long = QualType::plain(Type::Int(IntType {
                    kind: crate::types::IntKind::Long,
                    bits: 64,
                    signed: true,
                }));
                self.convert(&d, &long, &e.ty)
            }
            (BinOp::Add | BinOp::Sub, K::Ptr, K::Int(_)) => {
                let size = self.elem_size(&lhs.ty);
                let n = self.to_int(&b, &rhs.ty);
                let f = if op == BinOp::Add { "add" } else { "sub" };
                self.bind("Ptr", &format!("Ptr.{f} {a} {size} {n}"))
            }
            (BinOp::Add, K::Int(_), K::Ptr) => {
                let size = self.elem_size(&rhs.ty);
                let n = self.to_int(&a, &lhs.ty);
                self.bind("Ptr", &format!("Ptr.add {b} {size} {n}"))
            }
            _ => self.refuse("pointer arithmetic Achates does not recognise"),
        }
    }

    fn binary(&mut self, e: &Expr, op: BinOp, lhs: &Expr, rhs: &Expr) -> String {
        if matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge | BinOp::Eq | BinOp::Ne) {
            let c = self.compare(op, lhs, rhs);
            return self.of_bool(&c, &e.ty);
        }
        if self.kind(&lhs.ty) == K::Ptr || self.kind(&rhs.ty) == K::Ptr {
            return self.pointer_arith(e, op, lhs, rhs);
        }
        let a = self.rv(lhs);
        let b = self.rv(rhs);
        self.arith(op, &e.ty, &a, &b, &rhs.ty)
    }

    /// Runs `f` with its statements collected apart, `deeper` levels in.
    fn capture<R>(&mut self, deeper: usize, f: impl FnOnce(&mut Self) -> R) -> (R, Vec<String>) {
        let saved = std::mem::take(&mut self.out);
        self.ind += deeper;
        let r = f(self);
        self.ind -= deeper;
        (r, std::mem::replace(&mut self.out, saved))
    }

    fn logical(&mut self, op: LogicalOp, lhs: &Expr, rhs: &Expr) -> String {
        let a = self.cond(lhs);
        let (b, lines) = self.capture(1, |s| s.cond(rhs));
        let and = op == LogicalOp::And;
        if lines.is_empty() {
            return format!("({a} {} {b})", if and { "&&" } else { "||" });
        }
        let t = self.fresh("t");
        self.line(format!("let mut {t} : Bool := {}", !and));
        self.line(format!("if {}{a} then", if and { "" } else { "!" }));
        self.out.extend(lines);
        self.line(format!("  {t} := {b}"));
        t
    }

    fn conditional(&mut self, e: &Expr, cond: &Expr, then: &Expr, els: &Expr) -> String {
        let c = self.cond(cond);
        let (a, la) = self.capture(1, |s| s.rv(then));
        let (b, lb) = self.capture(1, |s| s.rv(els));
        let void = self.kind(&e.ty) == K::Void;
        if la.is_empty() && lb.is_empty() && !void {
            return format!("(if {c} then {a} else {b})");
        }
        let ty = self.lty(&e.ty);
        let t = self.fresh("t");
        self.line(format!("let mut {t} : {ty} := default"));
        self.line(format!("if {c} then"));
        self.out.extend(la);
        self.line(format!("  {t} := {a}"));
        self.line("else");
        self.out.extend(lb);
        self.line(format!("  {t} := {b}"));
        t
    }

    /// The value `old ± 1` as `++` and `--` compute it: in `int` for
    /// narrower types, since the operand is promoted first.
    fn step(&mut self, old: &str, t: &QualType, up: bool) -> String {
        let f = if up { "add" } else { "sub" };
        match self.kind(t) {
            K::Int(i) if i.bits < self.u.tu.target.int_bits => {
                let int = QualType::plain(Type::Int(IntType {
                    kind: crate::types::IntKind::Int,
                    bits: self.u.tu.target.int_bits,
                    signed: true,
                }));
                let wide = self.convert(old, t, &int);
                let ty = self.lty(&int);
                let sum = self.bind(&ty, &format!("SInt.{f} {wide} 1"));
                self.convert(&sum, &int, t)
            }
            K::Int(i) if i.signed => self.bind(&int_ty(i), &format!("SInt.{f} {old} 1")),
            K::Int(_) => format!("({old} {} 1)", if up { '+' } else { '-' }),
            K::Float(_) => {
                self.float_op();
                format!("({old} {} 1)", if up { '+' } else { '-' })
            }
            K::Ptr => {
                let size = self.elem_size(t);
                self.bind("Ptr", &format!("Ptr.{f} {old} {size} 1"))
            }
            _ => self.refuse(format!("increment of {t}")),
        }
    }

    fn incdec(&mut self, op: UnaryOp, operand: &Expr) -> String {
        let up = matches!(op, UnaryOp::PreInc | UnaryOp::PostInc);
        let post = matches!(op, UnaryOp::PostInc | UnaryOp::PostDec);
        let target = self.place(operand);
        let cur = self.load(target.clone_lv(), &operand.ty);
        let ty = self.lty(&operand.ty);
        // A variable held as a value is about to change under this name.
        let old = if post && matches!(target, Lv::Temp(_)) {
            let t = self.fresh("t");
            self.line(format!("let {t} : {ty} := {cur}"));
            t
        } else {
            cur
        };
        let new = self.step(&old, &operand.ty, up);
        let new = self.named(&new, &ty);
        self.store_lv(target, &operand.ty, &new);
        if post { old } else { new }
    }

    /// An lvalue with its address computed, so it can be used twice.
    fn place(&mut self, e: &Expr) -> Lv {
        match self.lv(e) {
            Lv::Mem(p, off) => Lv::Mem(self.at(&p, off), 0),
            t @ Lv::Temp(_) => t,
        }
    }

    /// Gives a compound term a name, so that later lines see one value.
    fn named(&mut self, term: &str, ty: &str) -> String {
        if term.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return term.to_owned();
        }
        let t = self.fresh("t");
        self.line(format!("let {t} : {ty} := {term}"));
        t
    }

    fn assign(&mut self, lhs: &Expr, rhs: &Expr) -> String {
        let target = self.place(lhs);
        let v = self.rv(rhs);
        let ty = self.lty(&lhs.ty);
        let v = self.named(&v, &ty);
        match &target {
            Lv::Temp(name) => {
                let name = name.clone();
                self.store_lv(target, &lhs.ty, &v);
                name
            }
            Lv::Mem(..) => {
                self.store_lv(target, &lhs.ty, &v);
                v
            }
        }
    }

    fn compound_assign(&mut self, e: &Expr) -> String {
        let ExprKind::CompoundAssign {
            op,
            lhs,
            rhs,
            compute_lhs,
            compute_result,
        } = &e.kind
        else {
            return self.refuse("not a compound assignment");
        };
        let target = self.place(lhs);
        let old = self.load(target.clone_lv(), &lhs.ty);
        let r = self.rv(rhs);
        let new = if self.kind(&lhs.ty) == K::Ptr {
            let size = self.elem_size(&lhs.ty);
            let n = self.to_int(&r, &rhs.ty);
            let f = if *op == BinOp::Add { "add" } else { "sub" };
            if !matches!(op, BinOp::Add | BinOp::Sub) {
                self.refuse("compound assignment to a pointer other than += and -=");
            }
            self.bind("Ptr", &format!("Ptr.{f} {old} {size} {n}"))
        } else {
            let a = self.convert(&old, &lhs.ty, compute_lhs);
            let v = self.arith(*op, compute_result, &a, &r, &rhs.ty);
            self.convert(&v, compute_result, &lhs.ty)
        };
        let ty = self.lty(&lhs.ty);
        let new = self.named(&new, &ty);
        let result = match &target {
            Lv::Temp(name) => name.clone(),
            Lv::Mem(..) => new.clone(),
        };
        self.store_lv(target, &lhs.ty, &new);
        result
    }

    fn unary(&mut self, e: &Expr, op: UnaryOp, operand: &Expr) -> String {
        match op {
            UnaryOp::Plus | UnaryOp::Extension => self.rv(operand),
            UnaryOp::Minus => {
                if let (ExprKind::IntLit(v), K::Int(i)) = (&operand.kind, self.kind(&e.ty))
                    && i.signed
                    && let Ok(v) = i128::try_from(*v)
                {
                    return self.lit(-v, i);
                }
                let a = self.rv(operand);
                match self.kind(&e.ty) {
                    K::Int(i) if i.signed => self.bind(&int_ty(i), &format!("SInt.neg {a}")),
                    K::Int(_) => format!("(UInt.neg {a})"),
                    K::Float(_) => format!("(-{a})"),
                    _ => self.refuse("negation of a non-arithmetic value"),
                }
            }
            UnaryOp::BitNot => {
                let a = self.rv(operand);
                match self.kind(&e.ty) {
                    K::Int(i) => format!("({}.bnot {a})", int_ns(i)),
                    _ => self.refuse("`~` on a non-integer"),
                }
            }
            UnaryOp::Not => {
                let c = self.cond(operand);
                self.of_bool(&format!("(!{c})"), &e.ty)
            }
            UnaryOp::AddrOf => {
                if matches!(operand.kind, ExprKind::Func { .. }) {
                    return self.fn_value(operand);
                }
                let l = self.lv(operand);
                self.addr(l)
            }
            UnaryOp::Deref => self.refuse("dereference used as a value without a load"),
            UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec => self.incdec(op, operand),
        }
    }

    fn member_value(&mut self, e: &Expr, base: &Expr, field: &str) -> String {
        let a = self.rv(base);
        let off = self.field_offset(&base.ty, field, &e.ty);
        let ty = self.lty(&e.ty);
        match self.kind(&e.ty) {
            K::Agg => {
                let size = self.size_align(&e.ty).map_or(0, |x| x.0);
                format!("(Agg.sub {a} {off} {size})")
            }
            _ => self.bind(&ty, &format!("Agg.get {ty} {a} {off}")),
        }
    }

    fn atomic(&mut self, op: &str, operands: &[Expr]) -> String {
        self.res.assumptions.insert(ATOMIC.to_owned());
        let pointee = operands.first().and_then(|p| match &p.ty.ty {
            Type::Pointer(t) => Some((**t).clone()),
            _ => None,
        });
        let (Some(p), Some(t)) = (operands.first(), pointee) else {
            return self.refuse(format!("atomic operation {op}"));
        };
        let ptr = self.rv(p);
        match (op, operands.get(2)) {
            ("__c11_atomic_load", None) => self.load(Lv::Mem(ptr, 0), &t),
            ("__c11_atomic_store", Some(v)) => {
                let v = self.rv(v);
                self.store_to(&ptr, 0, &t, &v);
                "()".into()
            }
            _ => self.refuse(format!("atomic operation {op}")),
        }
    }

    fn float_lit(&mut self, e: &Expr, text: &str, bits: u64) -> String {
        match self.kind(&e.ty) {
            K::Float(FloatKind::Double) => format!("(Float.ofBits 0x{bits:016x})"),
            // Parsed again at single precision: rounding the double would round twice.
            K::Float(FloatKind::Float) => match text.parse::<f32>() {
                Ok(f) => format!("(Float32.ofBits 0x{:08x})", f.to_bits()),
                Err(_) => self.refuse(format!("float literal `{text}`")),
            },
            _ => self.refuse("floating literal of a non-floating type"),
        }
    }

    fn int_const(&mut self, e: &Expr, v: i128) -> String {
        match self.kind(&e.ty) {
            K::Int(i) => self.lit(v, i),
            _ => self.refuse(format!("integer constant of type {}", e.ty)),
        }
    }

    /// The value of `e`, after emitting whatever computes it.
    pub(crate) fn rv(&mut self, e: &Expr) -> String {
        match &e.kind {
            ExprKind::IntLit(v) => match i128::try_from(*v) {
                Ok(v) => self.int_const(e, v),
                Err(_) => self.refuse("integer literal too large"),
            },
            ExprKind::CharLit(v) => self.int_const(e, i128::from(*v)),
            ExprKind::EnumConst { value, .. } => self.int_const(e, *value),
            ExprKind::TypeTrait { value, .. } => self.int_const(e, i128::from(*value)),
            ExprKind::FloatLit { text, bits } => self.float_lit(e, text, *bits),
            ExprKind::Unary { op, operand } => self.unary(e, *op, operand),
            ExprKind::Binary { op, lhs, rhs } => self.binary(e, *op, lhs, rhs),
            ExprKind::Logical { op, lhs, rhs } => {
                let c = self.logical(*op, lhs, rhs);
                self.of_bool(&c, &e.ty)
            }
            ExprKind::Comma { lhs, rhs } => {
                self.effect(lhs);
                self.rv(rhs)
            }
            ExprKind::Assign { lhs, rhs } => self.assign(lhs, rhs),
            ExprKind::CompoundAssign { .. } => self.compound_assign(e),
            ExprKind::Cond { cond, then, els } => self.conditional(e, cond, then, els),
            ExprKind::Call { callee, args, direct } => self.call(e, callee, args, direct.as_deref()),
            ExprKind::Member { base, field, arrow: false } if !e.lvalue => self.member_value(e, base, field),
            ExprKind::Cast { kind, operand, .. } => self.cast(e, *kind, operand),
            ExprKind::Atomic { op, operands } => self.atomic(op, operands),
            ExprKind::Unsupported(u) => self.refuse(format!("{}: {}", u.clang_kind, u.reason)),
            ExprKind::CompoundLiteral(_) | ExprKind::InitList { .. } | ExprKind::ImplicitValueInit => {
                self.refuse("initialiser used as a value")
            }
            _ => self.refuse("object used as a value without a load"),
        }
    }

    /// The truth of `e` as a Lean `Bool`.
    pub(crate) fn cond(&mut self, e: &Expr) -> String {
        match &e.kind {
            ExprKind::Binary { op, lhs, rhs }
                if matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge | BinOp::Eq | BinOp::Ne) =>
            {
                self.compare(*op, lhs, rhs)
            }
            ExprKind::Logical { op, lhs, rhs } => self.logical(*op, lhs, rhs),
            ExprKind::Unary {
                op: UnaryOp::Not,
                operand,
            } => {
                let c = self.cond(operand);
                format!("(!{c})")
            }
            _ => {
                let v = self.rv(e);
                match self.kind(&e.ty) {
                    K::Bool => v,
                    K::Int(_) | K::Float(_) => format!("({v} != 0)"),
                    K::Ptr => format!("({v} != Ptr.null)"),
                    _ => self.refuse("condition that is not a scalar"),
                }
            }
        }
    }

    /// Evaluates `e` for its effects.
    pub(crate) fn effect(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Comma { lhs, rhs } => {
                self.effect(lhs);
                self.effect(rhs);
            }
            ExprKind::Cast {
                kind: CastKind::ToVoid,
                operand,
                ..
            } => self.effect(operand),
            _ => {
                self.rv(e);
            }
        }
    }

    fn init_array(&mut self, ptr: &str, off: u64, elem: &QualType, len: u64, elems: &[Expr], filler: Option<&Expr>) {
        let Some((esize, _)) = self.size_align(elem) else { return };
        let scalar = !matches!(self.kind(elem), K::Agg | K::Void | K::Bad);
        let mut batch: Vec<String> = Vec::new();
        let mut batch_at = off;
        let mut at = off;
        for e in elems {
            let direct = scalar && !matches!(e.kind, ExprKind::InitList { .. } | ExprKind::ImplicitValueInit);
            if direct {
                let (v, lines) = self.capture(0, |s| s.rv(e));
                if !lines.is_empty() || batch.len() >= 64 {
                    self.flush(ptr, batch_at, &mut batch);
                    batch_at = at;
                }
                self.out.extend(lines);
                batch.push(v);
            } else {
                self.flush(ptr, batch_at, &mut batch);
                self.init_at(ptr, at, elem, e);
                batch_at = at + esize;
            }
            at += esize;
        }
        self.flush(ptr, batch_at, &mut batch);
        let rest = len.saturating_sub(elems.len() as u64);
        match filler {
            _ if rest == 0 => {}
            Some(f) if matches!(f.kind, ExprKind::ImplicitValueInit) => {
                let p = self.at(ptr, at);
                self.line(format!("Mem.zero {p} {}", rest * esize));
            }
            Some(f) if rest <= 64 => {
                for i in 0..rest {
                    self.init_at(ptr, at + i * esize, elem, f);
                }
            }
            _ => {
                self.refuse("array initialiser with a long non-zero filler");
            }
        }
    }

    fn flush(&mut self, ptr: &str, off: u64, batch: &mut Vec<String>) {
        if batch.is_empty() {
            return;
        }
        let p = self.at(ptr, off);
        self.line(format!("Mem.storeList {p} [{}]", batch.join(", ")));
        batch.clear();
    }

    fn init_record(&mut self, ptr: &str, off: u64, t: &QualType, elems: &[Expr], union_field: Option<&str>) {
        let Some(key) = self.record_of(t) else { return };
        let fields = self.u.tu.records.get(&key).and_then(|d| d.fields.clone()).unwrap_or_default();
        if fields.iter().any(|f| f.bit_width.is_some()) {
            self.refuse("initialiser of a record with bit-fields");
            return;
        }
        if key.0 == RecordKind::Union {
            let f = union_field.and_then(|n| fields.iter().find(|f| f.name == n));
            match (f, elems.first()) {
                (Some(f), Some(e)) => {
                    let fo = self.field_offset(t, &f.name, &f.ty);
                    self.init_at(ptr, off + fo, &f.ty, e);
                }
                (None, None) => {}
                _ => {
                    self.refuse("union initialiser Achates cannot match to a member");
                }
            }
            return;
        }
        if elems.len() > fields.len() {
            self.refuse("more initialisers than members");
        }
        for (f, e) in fields.iter().zip(elems) {
            let fo = self.field_offset(t, &f.name, &f.ty);
            self.init_at(ptr, off + fo, &f.ty, e);
        }
    }

    /// Initialises the object of type `t` at `ptr + off` from `e`.
    pub(crate) fn init_at(&mut self, ptr: &str, off: u64, t: &QualType, e: &Expr) {
        match (&e.kind, &t.ty) {
            (ExprKind::InitList { elems, filler, .. }, Type::Array { elem, len: Some(n) }) => {
                self.init_array(ptr, off, elem, *n, elems, filler.as_deref());
            }
            (ExprKind::InitList { elems, union_field, .. }, Type::Record { .. }) => {
                self.init_record(ptr, off, t, elems, union_field.as_deref());
            }
            (ExprKind::InitList { elems, .. }, _) => match elems.first() {
                Some(e) if elems.len() == 1 => self.init_at(ptr, off, t, e),
                _ => {
                    self.refuse("braced initialiser of a scalar");
                }
            },
            (ExprKind::ImplicitValueInit, _) => {
                if let Some((size, _)) = self.size_align(t) {
                    let p = self.at(ptr, off);
                    self.line(format!("Mem.zero {p} {size}"));
                }
            }
            (ExprKind::StringLit(bytes), Type::Array { len: Some(n), .. }) => {
                let p = self.at(ptr, off);
                let keep: Vec<String> = bytes.iter().take(usize::try_from(*n).unwrap_or(0)).map(u8::to_string).collect();
                self.line(format!("Mem.zero {p} {n}"));
                if !keep.is_empty() {
                    self.line(format!("Mem.storeRaw {p} [{}]", keep.join(", ")));
                }
            }
            _ => {
                let v = self.rv(e);
                self.store_to(ptr, off, t, &v);
            }
        }
    }

    fn builtin(&mut self, e: &Expr, name: &str, args: &[Expr]) -> String {
        match (name, args) {
            ("__builtin_expect", [x, hint]) => {
                let (_, lines) = self.capture(0, |s| s.rv(hint));
                if !lines.is_empty() {
                    self.refuse("__builtin_expect with a hint that has effects");
                }
                self.rv(x)
            }
            ("__builtin_unreachable", []) => {
                self.line("ub \"__builtin_unreachable was reached\"");
                "()".into()
            }
            ("__builtin_isfinite" | "__builtin_isnan", [x]) if matches!(self.kind(&x.ty), K::Float(_)) => {
                let v = self.rv(x);
                let f = if name == "__builtin_isnan" { "isNaN" } else { "isFinite" };
                self.of_bool(&format!("({v}.{f})"), &e.ty)
            }
            _ if name.starts_with("__builtin_va_") => {
                self.refuse("variadic argument handling (va_start and friends) is not modelled")
            }
            _ => self.refuse(format!("compiler builtin `{name}` is not modelled")),
        }
    }

    fn var_arg(&mut self, v: &str, t: &QualType) -> String {
        match self.kind(t) {
            K::Int(i) if i.signed => format!("(VArg.sint {v})"),
            K::Int(_) => format!("(VArg.uint {v})"),
            K::Float(FloatKind::Double) => format!("(VArg.f64 {v})"),
            K::Ptr => format!("(VArg.ptr {v})"),
            K::Agg => format!("(VArg.agg {v})"),
            _ => self.refuse(format!("argument of type {t} passed through `...`")),
        }
    }

    /// The Lean application for a call to what `name` means here.
    fn callee_text(&mut self, name: &str, sig: &Sig) -> Option<String> {
        let (u, module) = (self.u, self.module.clone());
        let target = match u.target(self.w, name, &module) {
            Target::Emitted(meta) => Ok((meta.key.clone(), meta.module.clone(), meta.name.clone(), meta.sig.clone())),
            Target::Model(m) if m.sig == sig.arrow() => {
                self.res.models.insert(m.name.to_owned());
                self.res.assumptions.extend(m.assumes.iter().map(|a| (*a).to_owned()));
                return Some(m.lean.to_owned());
            }
            Target::Model(m) => Err(m.name.to_owned()),
            Target::Ext(n) => Err(n),
        };
        match target {
            Ok((key, module, fname, Ok(def))) if def == *sig && !def.variadic => {
                self.res.callees.insert(key);
                Some(format!("{module}.{} fuel", names::ident(&fname)))
            }
            Ok((key, ..)) | Err(key) => match self.w.ext(&key, sig) {
                Ok(class) => {
                    self.res.exts.insert(key);
                    Some(format!("{class}.call"))
                }
                Err(e) => {
                    self.refuse(e);
                    None
                }
            },
        }
    }

    fn indirect(&mut self, callee: &Expr, sig: &Sig) -> String {
        let p = self.rv(callee);
        let cands: Vec<String> = self
            .w
            .addressed
            .iter()
            .filter(|(_, s)| s.as_ref() == Some(sig))
            .map(|(id, _)| id.clone())
            .collect();
        let mut text = format!("(match {p} with");
        for id in cands {
            // A key names a selection function; anything else is a C name.
            let by_key = self.w.fns.get(&id).map(|m| (m.key.clone(), m.module.clone(), m.name.clone()));
            let app = match by_key {
                Some((key, module, fname)) if !self.w.refused.contains(&key) && self.w.importable(&self.module, &module) => {
                    self.res.callees.insert(key);
                    Some(format!("{module}.{} fuel", names::ident(&fname)))
                }
                Some((key, ..)) => self.w.ext(&key, sig).ok().map(|c| {
                    self.res.exts.insert(key);
                    format!("{c}.call")
                }),
                None => self.callee_text(&id, sig),
            };
            if let Some(app) = app {
                text.push_str(&format!("\n{}  | Ptr.fn \"{id}\" => {app} ARGS", "  ".repeat(self.ind)));
            }
        }
        let pad = "  ".repeat(self.ind);
        text.push_str(&format!("\n{pad}  | Ptr.null => ub \"call through a null pointer\""));
        text.push_str(&format!(
            "\n{pad}  | _ => unsupported \"call through a pointer to a function the selection does not know with this type\")"
        ));
        text
    }

    fn call(&mut self, e: &Expr, callee: &Expr, args: &[Expr], direct: Option<&str>) -> String {
        if let Some(name) = direct
            && matches!(&callee.kind, ExprKind::Cast { operand, .. } if matches!(operand.kind, ExprKind::Func { builtin: true, .. }))
        {
            return self.builtin(e, name, args);
        }
        if self.in_static {
            return self.refuse("function call in a static initialiser");
        }
        let ft = match &callee.ty.ty {
            Type::Pointer(p) => match &p.ty {
                Type::Function(ft) => Some((**ft).clone()),
                _ => None,
            },
            _ => None,
        };
        let Some(sig) = ft.as_ref().and_then(|ft| self.sig_of(ft)) else {
            return self.refuse("call of something that is not a function with a prototype");
        };
        if args.len() < sig.params.len() || (args.len() > sig.params.len() && !sig.variadic) {
            return self.refuse("call with a number of arguments its prototype does not take");
        }
        // The callee of an indirect call is evaluated first, then the
        // arguments left to right; `check_order` has refused the cases
        // where another order could give another result.
        let head = match direct {
            Some(name) => self.callee_text(name, &sig).map(|h| format!("{h} ARGS")),
            None => Some(self.indirect(callee, &sig)),
        };
        let mut fixed = Vec::new();
        let mut extra = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let v = self.rv(a);
            if i < sig.params.len() {
                fixed.push(v);
            } else {
                extra.push(self.var_arg(&v, &a.ty));
            }
        }
        if sig.variadic {
            fixed.push(format!("[{}]", extra.join(", ")));
        }
        let Some(head) = head else { return "default".into() };
        let app = head.replace(" ARGS", &fixed.iter().map(|a| format!(" {a}")).collect::<String>());
        if sig.ret == "Unit" {
            self.line(app);
            "()".into()
        } else {
            self.bind(&sig.ret, &app)
        }
    }
}

impl Lv {
    fn clone_lv(&self) -> Self {
        match self {
            Self::Temp(n) => Self::Temp(n.clone()),
            Self::Mem(p, o) => Self::Mem(p.clone(), *o),
        }
    }
}
