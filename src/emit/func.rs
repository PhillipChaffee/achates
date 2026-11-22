//! Statements: one C function body as the lines of a Lean `do` block.
//!
//! Lean's `do` notation supplies mutable variables, `return`, and `break`
//! and `continue` for the innermost `for`. Every C jump is expressed with
//! those: a jump that leaves more than one Lean loop sets a flag, breaks,
//! and is passed on by a check after each loop on the way out.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::emit::names::{self, Sig};
use crate::emit::order::{Assume, Classes, OrderCx, VarKey, Verdict, classify};
use crate::emit::world::{BLOCK_ORDER, EXT_ORDER, EXT_READS, Unit, World, call_effect};
use crate::ir::{Decl, Expr, Function, LocalVar, Stmt};
use crate::types::{QualType, Type};

#[derive(Debug, Clone)]
pub(crate) enum VarInfo {
    /// A Lean variable holding the value.
    Temp(String),
    /// A Lean term for the address of the object.
    Mem(String),
}

struct Frame {
    /// Index of the line reserved for the flags declared before this loop.
    marker: usize,
    indent: usize,
    flags: Vec<String>,
    /// Checks to emit after this loop: flag, and what to do when it is set.
    post: Vec<(String, &'static str)>,
}

/// What one function's emission produced.
#[derive(Debug, Default)]
pub(crate) struct Emitted {
    pub(crate) lines: Vec<String>,
    pub(crate) reasons: Vec<String>,
    pub(crate) exts: BTreeSet<String>,
    pub(crate) callees: BTreeSet<String>,
    pub(crate) models: BTreeSet<String>,
    pub(crate) assumptions: BTreeSet<String>,
}

pub(crate) struct FnEmitter<'a> {
    pub(crate) u: &'a Unit<'a>,
    pub(crate) w: &'a mut World,
    /// The Lean module the code is written into.
    pub(crate) module: String,
    /// Key of the function being emitted; empty for a static initialiser.
    pub(crate) key: String,
    pub(crate) fname: String,
    pub(crate) out: Vec<String>,
    pub(crate) ind: usize,
    pub(crate) tmp: u32,
    pub(crate) vars: BTreeMap<VarKey, VarInfo>,
    pub(crate) temps: BTreeSet<VarKey>,
    pub(crate) statics: BTreeMap<u32, String>,
    frames: Vec<Frame>,
    labels: Vec<(String, usize)>,
    breaks: Vec<usize>,
    /// Frame a `continue` goes to, and whether it re-enters that loop
    /// (`true`) or leaves it (`false`, for a body wrapped in a `Once`).
    conts: Vec<(usize, bool)>,
    /// Addresses of the function's memory objects, freed on return.
    pub(crate) frame_objs: Vec<(String, u64, u64)>,
    /// True while emitting the initialiser of a static object.
    pub(crate) in_static: bool,
    pub(crate) res: Emitted,
    pub(crate) ret: Option<QualType>,
    /// In a variadic function, the Lean name of the number of its `...`
    /// arguments (`VaList.enter`).
    pub(crate) va_args: Option<String>,
    /// In a function that uses `va_start`, `va_copy` or `va_end`, the Lean
    /// name of the number of this call (`VaList.call`).
    pub(crate) va_call: Option<String>,
}

impl<'a> FnEmitter<'a> {
    pub(crate) fn new(
        u: &'a Unit<'a>,
        w: &'a mut World,
        module: &str,
        key: &str,
        fname: &str,
    ) -> Self {
        Self {
            u,
            w,
            module: module.to_owned(),
            key: key.to_owned(),
            fname: fname.to_owned(),
            out: Vec::new(),
            ind: 1,
            tmp: 0,
            vars: BTreeMap::new(),
            temps: BTreeSet::new(),
            statics: BTreeMap::new(),
            frames: Vec::new(),
            labels: Vec::new(),
            breaks: Vec::new(),
            conts: Vec::new(),
            frame_objs: Vec::new(),
            in_static: false,
            res: Emitted::default(),
            ret: None,
            va_args: None,
            va_call: None,
        }
    }

    pub(crate) fn refuse(&mut self, reason: impl Into<String>) -> String {
        let r = reason.into();
        if !self.res.reasons.contains(&r) {
            self.res.reasons.push(r);
        }
        "default".to_owned()
    }

    pub(crate) fn line(&mut self, s: impl AsRef<str>) {
        self.out
            .push(format!("{}{}", "  ".repeat(self.ind), s.as_ref()));
    }

    pub(crate) fn fresh(&mut self, prefix: &str) -> String {
        self.tmp += 1;
        format!("{prefix}{}", self.tmp)
    }

    /// `let tN : ty ← action`, giving `tN`.
    pub(crate) fn bind(&mut self, ty: &str, action: &str) -> String {
        let t = self.fresh("t");
        self.line(format!("let {t} : {ty} ← {action}"));
        t
    }

    /// A Lean block must end in an action, not in a `let`.
    fn close_block(&mut self, start: usize) {
        let needs = self.out.len() == start
            || self
                .out
                .last()
                .is_some_and(|l| l.trim_start().starts_with("let "));
        if needs {
            self.line("pure ()");
        }
    }

    fn open_frame(&mut self, header: &str) -> usize {
        let marker = self.out.len();
        self.out.push(String::new());
        self.frames.push(Frame {
            marker,
            indent: self.ind,
            flags: Vec::new(),
            post: Vec::new(),
        });
        self.line(header);
        self.ind += 1;
        self.frames.len() - 1
    }

    fn close_frame(&mut self, start: usize) {
        self.close_block(start);
        self.ind -= 1;
        let Some(fr) = self.frames.pop() else { return };
        let decls: Vec<String> = fr
            .flags
            .iter()
            .map(|f| format!("{}let mut {f} := false", "  ".repeat(fr.indent)))
            .collect();
        if let Some(slot) = self.out.get_mut(fr.marker) {
            *slot = decls.join("\n");
        }
        for (flag, action) in fr.post {
            self.line(format!("if {flag} then {action}"));
        }
    }

    /// Leaves Lean loop `target` (`reenter` false) or starts its next
    /// round (`reenter` true), from anywhere inside it.
    fn jump(&mut self, target: usize, reenter: bool) {
        let cur = self.frames.len().saturating_sub(1);
        let word = if reenter { "continue" } else { "break" };
        if cur == target {
            self.line(word);
            return;
        }
        let flag = self.fresh("j");
        for (i, fr) in self.frames.iter_mut().enumerate().skip(target + 1) {
            if i == target + 1 {
                fr.flags.push(flag.clone());
                fr.post.push((flag.clone(), word));
            } else {
                fr.post.push((flag.clone(), "break"));
            }
        }
        self.line(format!("{flag} := true"));
        self.line("break");
    }

    /// Emits statements until one does not fall through; the rest would be
    /// dead code, which Lean warns about.
    fn seq<'s>(&mut self, stmts: impl IntoIterator<Item = &'s Stmt>) -> bool {
        for s in stmts {
            if !self.stmt(s) {
                return false;
            }
        }
        true
    }

    /// A block: with labels in it, the statements before each label go in a
    /// `Once` loop, so that `goto` to the label is a `break` out of it.
    fn block(&mut self, v: &[Stmt]) -> bool {
        let labels: Vec<(usize, &str)> = v
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match s {
                Stmt::Label { name, .. } => Some((i, name.as_str())),
                _ => None,
            })
            .collect();
        if labels.is_empty() {
            return self.seq(v);
        }
        let mut starts = Vec::new();
        for (_, name) in labels.iter().rev() {
            starts.push(self.out.len() + 2);
            let fr = self.open_frame("for _ in Once.mk do");
            self.labels.push(((*name).to_owned(), fr));
        }
        let mut from = 0;
        let mut falls = true;
        for (at, _) in &labels {
            if falls {
                self.seq(v.iter().take(*at).skip(from));
            }
            self.labels.pop();
            let start = starts.pop().unwrap_or(0);
            self.close_frame(start);
            from = *at + 1;
            // A label is reachable through `goto` whatever came before it.
            falls = match v.get(*at) {
                Some(Stmt::Label { body, .. }) => self.stmt(body),
                _ => true,
            };
        }
        falls && self.seq(v.iter().skip(from))
    }

    fn nested(&mut self, s: &Stmt) -> bool {
        self.ind += 1;
        let start = self.out.len();
        let falls = self.stmt(s);
        self.close_block(start);
        self.ind -= 1;
        falls
    }

    fn if_stmt(&mut self, cond: &Expr, then: &Stmt, els: Option<&Stmt>) -> bool {
        let c = self.full_cond(cond);
        self.line(format!("if {c} then"));
        let a = self.nested(then);
        let b = els.is_none_or(|e| {
            self.line("else");
            self.nested(e)
        });
        a || b
    }

    fn loop_stmt(
        &mut self,
        pre: Option<&Expr>,
        body: &Stmt,
        inc: Option<&Expr>,
        post: Option<&Expr>,
    ) {
        let start = self.out.len() + 2;
        let lp = self.open_frame("for _ in Fuel.mk fuel do");
        if let Some(c) = pre {
            let c = self.full_cond(c);
            self.line(format!("if !{c} then break"));
        }
        self.breaks.push(lp);
        // `continue` must still run the increment and the `do`-`while`
        // condition, so their bodies get a loop of their own to leave.
        let wrap = inc.is_some() || post.is_some();
        if wrap {
            let bstart = self.out.len() + 2;
            let b = self.open_frame("for _ in Once.mk do");
            self.conts.push((b, false));
            self.stmt(body);
            self.close_frame(bstart);
        } else {
            self.conts.push((lp, true));
            self.stmt(body);
        }
        self.conts.pop();
        self.breaks.pop();
        if let Some(e) = inc {
            self.full_effect(e);
        }
        if let Some(c) = post {
            let c = self.full_cond(c);
            self.line(format!("if !{c} then break"));
        }
        self.close_frame(start);
    }

    fn switch_stmt(&mut self, cond: &Expr, body: &Stmt) {
        let Stmt::Compound(items) = body else {
            self.refuse("switch whose body is not a block");
            return;
        };
        let mut sections: Vec<(Vec<Option<&Expr>>, Vec<&Stmt>)> = Vec::new();
        for s in items {
            let mut labels = Vec::new();
            let mut cur = s;
            loop {
                match cur {
                    Stmt::Case { expr, body, .. } => {
                        labels.push(Some(expr));
                        cur = body;
                    }
                    Stmt::Default { body } => {
                        labels.push(None);
                        cur = body;
                    }
                    _ => break,
                }
            }
            if !labels.is_empty() {
                sections.push((labels, vec![cur]));
            } else if let Some(last) = sections.last_mut() {
                last.1.push(cur);
            } else if !matches!(cur, Stmt::Decl(_) | Stmt::Null) {
                self.refuse("statement before the first case label of a switch");
            }
        }
        let v = self.full_rv(cond);
        let sw = self.fresh("t");
        self.line(format!("let {sw} := {v}"));
        let mut default = sections.len();
        let mut chain = String::new();
        for (i, (labels, _)) in sections.iter().enumerate() {
            let mut tests = Vec::new();
            for l in labels {
                match l {
                    None => default = i,
                    Some(e) => {
                        let before = self.out.len();
                        let c = self.rv(e);
                        if self.out.len() != before {
                            self.refuse("case label that is not a constant");
                        }
                        tests.push(format!("{sw} == {c}"));
                    }
                }
            }
            if !tests.is_empty() {
                let _ = write!(chain, "if {} then {i} else ", tests.join(" || "));
            }
        }
        let sel = self.fresh("t");
        self.line(format!("let {sel} : Nat := {chain}{default}"));
        let start = self.out.len() + 2;
        let fr = self.open_frame("for _ in Once.mk do");
        self.breaks.push(fr);
        for (i, (_, stmts)) in sections.iter().enumerate() {
            self.line(format!("if {sel} ≤ {i} then"));
            self.ind += 1;
            let s = self.out.len();
            self.seq(stmts.iter().copied());
            self.close_block(s);
            self.ind -= 1;
        }
        self.breaks.pop();
        self.close_frame(start);
    }

    fn local(&mut self, v: &LocalVar) {
        if !v.attrs.iter().all(|a| a == "unused" || a == "used") {
            self.refuse(format!("attribute on local `{}`", v.name));
        }
        match self.vars.get(&VarKey::Local(v.id)).cloned() {
            Some(VarInfo::Temp(name)) => {
                let ty = self.lty(&v.ty);
                let val = v
                    .init
                    .as_ref()
                    .map_or_else(|| "default".into(), |e| self.full_rv(e));
                self.line(format!("let mut {name} : {ty} := {val}"));
            }
            Some(VarInfo::Mem(ptr)) => match &v.init {
                Some(e) => {
                    self.check_order(e);
                    self.init_at(&ptr, 0, &v.ty, e);
                }
                None => {
                    if let Some((size, _)) = self.size_align(&v.ty) {
                        self.line(format!("Mem.undefine {ptr} {size}"));
                    }
                }
            },
            // A static local is initialised once, before the program starts.
            None => {}
        }
    }

    pub(crate) fn stmt(&mut self, s: &Stmt) -> bool {
        match s {
            Stmt::Compound(v) => return self.block(v),
            Stmt::Decl(ds) => {
                for d in ds {
                    match d {
                        Decl::Var(v) => self.local(v),
                        Decl::Unsupported(u) => {
                            self.refuse(format!("{}: {}", u.clang_kind, u.reason));
                        }
                    }
                }
            }
            Stmt::Expr(e) => self.full_effect(e),
            Stmt::If { cond, then, els } => return self.if_stmt(cond, then, els.as_deref()),
            Stmt::While { cond, body } => self.loop_stmt(Some(cond), body, None, None),
            Stmt::DoWhile { body, cond } => self.loop_stmt(None, body, None, Some(cond)),
            Stmt::For {
                init,
                cond,
                inc,
                body,
            } => {
                if let Some(i) = init {
                    self.stmt(i);
                }
                self.loop_stmt(cond.as_deref(), body, inc.as_deref(), None);
            }
            Stmt::Switch { cond, body } => self.switch_stmt(cond, body),
            Stmt::Case { .. } | Stmt::Default { .. } => {
                self.refuse("case label nested inside a statement of its switch");
            }
            Stmt::Break => return self.jump_to(self.breaks.last().map(|f| (*f, false)), "break"),
            Stmt::Continue => return self.jump_to(self.conts.last().copied(), "continue"),
            Stmt::Goto(name) => {
                let target = self
                    .labels
                    .iter()
                    .rev()
                    .find(|(n, _)| n == name)
                    .map(|(_, f)| (*f, false));
                if target.is_none() {
                    self.refuse(
                        "goto that is not a forward jump out to a label of an enclosing block",
                    );
                }
                return self.jump_to(target, "goto");
            }
            Stmt::Return(e) => {
                let v = e
                    .as_ref()
                    .map_or_else(|| "()".to_owned(), |e| self.full_rv(e));
                self.line(format!("return {v}"));
                return false;
            }
            Stmt::Label { .. } => {
                self.refuse("label that is not directly in a block");
            }
            Stmt::Null => {}
            Stmt::Unsupported(u) => {
                self.refuse(format!("{}: {}", u.clang_kind, u.reason));
            }
        }
        true
    }

    fn jump_to(&mut self, target: Option<(usize, bool)>, what: &str) -> bool {
        match target {
            Some((frame, reenter)) => self.jump(frame, reenter),
            None => {
                self.refuse(format!("{what} outside any statement it can leave"));
            }
        }
        false
    }

    pub(crate) fn check_order(&mut self, e: &Expr) {
        let mut verdict = Verdict::default();
        {
            let (unit, world) = (self.u, &*self.w);
            let key_of = |n: &str| unit.fn_key(world, n).cloned();
            let summary = |k: &str| world.summaries.get(k).copied();
            let effect = |call: &Expr| call_effect(call, &key_of, &summary, &world.addr_taken);
            let member = |record: &QualType, field: &str| -> Option<(u64, u64)> {
                let Type::Record { kind, name } = &record.ty else {
                    return None;
                };
                let key = (*kind, name.clone());
                let fields = unit.tu.records.get(&key)?.fields.as_ref()?;
                let i = fields
                    .iter()
                    .position(|f| !f.name.is_empty() && f.name == field)?;
                let f = fields.get(i)?;
                if f.bit_width.is_some() {
                    return None;
                }
                let off = unit.lay.records.get(&key)?.offsets.get(i)?.clone().ok()?;
                let (size, _) = unit.lay.size_align(&f.ty).ok()?;
                Some((off, size))
            };
            let cx = OrderCx {
                temps: &self.temps,
                call_effect: &effect,
                member: &member,
            };
            cx.eval(e, &mut verdict);
        }
        if verdict.refused {
            self.refuse(
                "an expression whose operands C does not sequence may interfere, so its value could depend on the compiler's order",
            );
        } else {
            for a in verdict.assumes {
                let text = match a {
                    Assume::ExternalOrder => EXT_ORDER,
                    Assume::BlockNumbering => BLOCK_ORDER,
                    Assume::ExternalReads => EXT_READS,
                };
                self.res.assumptions.insert(text.to_owned());
            }
        }
    }

    fn full_rv(&mut self, e: &Expr) -> String {
        self.check_order(e);
        self.rv(e)
    }

    fn full_cond(&mut self, e: &Expr) -> String {
        self.check_order(e);
        self.cond(e)
    }

    fn full_effect(&mut self, e: &Expr) {
        self.check_order(e);
        self.effect(e);
    }

    /// Declares the function's variables: scalars that are never addressed
    /// become Lean values, everything else an object in memory.
    fn declare(&mut self, f: &Function, classes: &Classes) -> Vec<String> {
        let mut used = BTreeSet::new();
        let mut params = Vec::new();
        for (i, p) in f.params.iter().enumerate() {
            let base = if p.name.is_empty() {
                format!("arg{i}")
            } else {
                names::local(&p.name)
            };
            let arg = if used.insert(base.clone()) {
                base
            } else {
                format!("{base}_{i}")
            };
            used.insert(arg.clone());
            let ty = self.lty(&p.ty);
            params.push(format!("({arg} : {ty})"));
            let key = VarKey::Param(i);
            if classes.temps.contains(&key) {
                let name = format!("{arg}_v");
                used.insert(name.clone());
                self.line(format!("let mut {name} : {ty} := {arg}"));
                self.vars.insert(key, VarInfo::Temp(name));
            } else if let Some((size, align)) = self.size_align(&p.ty) {
                let ptr = format!("{arg}_p");
                used.insert(ptr.clone());
                self.frame_objs.push((ptr.clone(), size, align));
                self.store_to(&ptr, 0, &p.ty, &arg);
                self.vars.insert(key, VarInfo::Mem(ptr));
            }
        }
        for (id, name, ty) in &classes.memory {
            let ptr = format!("{}_{id}", names::local(name));
            if let Some((size, align)) = self.size_align(ty) {
                self.frame_objs.push((ptr.clone(), size, align));
            }
            self.vars.insert(VarKey::Local(*id), VarInfo::Mem(ptr));
        }
        params
    }

    fn collect_locals(&mut self, s: &Stmt, classes: &Classes) {
        match s {
            Stmt::Compound(v) => v.iter().for_each(|s| self.collect_locals(s, classes)),
            Stmt::Decl(ds) => {
                for d in ds {
                    if let Decl::Var(v) = d {
                        let key = VarKey::Local(v.id);
                        if classes.temps.contains(&key) {
                            let name = format!("{}_{}", names::local(&v.name), v.id);
                            self.vars.insert(key, VarInfo::Temp(name));
                        } else if classes.statics.contains(&v.id) {
                            self.static_local(v);
                        }
                    }
                }
            }
            Stmt::If { then, els, .. } => {
                self.collect_locals(then, classes);
                if let Some(e) = els {
                    self.collect_locals(e, classes);
                }
            }
            Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::Switch { body, .. }
            | Stmt::Case { body, .. }
            | Stmt::Default { body }
            | Stmt::Label { body, .. } => self.collect_locals(body, classes),
            Stmt::For { init, body, .. } => {
                if let Some(i) = init {
                    self.collect_locals(i, classes);
                }
                self.collect_locals(body, classes);
            }
            _ => {}
        }
    }

    fn static_local(&mut self, v: &LocalVar) {
        let key = format!("{}.{}.{}", self.module, self.fname, v.name);
        let lean = format!(
            "s_{}_{}_{}",
            self.module.replace('.', "_"),
            self.fname,
            v.name
        );
        match self.static_object(&key, &lean, &v.ty, v.init.as_ref()) {
            Ok(term) => {
                self.statics.insert(v.id, term);
            }
            Err(e) => {
                self.refuse(format!("static local `{}`: {e}", v.name));
            }
        }
    }

    /// Registers an object with static storage and emits its initialiser.
    pub(crate) fn static_object(
        &mut self,
        key: &str,
        lean: &str,
        ty: &QualType,
        init: Option<&Expr>,
    ) -> Result<String, String> {
        let (size, align) = self.u.lay.size_align(ty)?;
        let lean = names::ident(lean);
        let term = format!("Statics.{lean}");
        let id = self
            .w
            .statics
            .object(key, lean, size, align, ty.quals.is_const || elem_const(ty));
        if let Some(e) = init {
            let saved = (
                std::mem::take(&mut self.out),
                self.ind,
                self.in_static,
                self.res.reasons.len(),
            );
            self.ind = 1;
            self.in_static = true;
            self.init_at(&term, 0, ty, e);
            let lines = std::mem::replace(&mut self.out, saved.0);
            self.ind = saved.1;
            self.in_static = saved.2;
            if self.res.reasons.len() > saved.3 {
                let why = self.res.reasons.split_off(saved.3).join("; ");
                self.w
                    .statics
                    .globals
                    .insert(key.to_owned(), Err(why.clone()));
                return Err(why);
            }
            self.w.statics.inits.push((id, lines));
        }
        Ok(term)
    }

    /// The body of `f` as `do`-block lines, with the parameter list.
    pub(crate) fn function(mut self, f: &Function) -> (Emitted, Vec<String>, Option<Sig>) {
        let classes = classify(f);
        self.temps.clone_from(&classes.temps);
        self.ret = Some(f.ret.clone());
        self.ind = 2;
        let mut params = self.declare(f, &classes);
        let mut prologue = Vec::new();
        let mut epilogue = Vec::new();
        if f.variadic {
            params.push("(«variadic args» : List VArg)".to_owned());
            prologue.push("let «va args» ← VaList.enter «variadic args»".to_owned());
            epilogue.push("VaList.leave «va args»".to_owned());
            self.va_args = Some("«va args»".into());
        }
        if uses_va_macros(f) {
            prologue.push("let «va call» ← VaList.call".to_owned());
            epilogue.insert(0, "VaList.checkEnded «va call»".to_owned());
            self.va_call = Some("«va call»".into());
        }
        self.collect_locals(&f.body, &classes);
        let ret = self.lty(&f.ret);
        let falls = self.stmt(&f.body);
        if falls {
            if matches!(f.ret.ty, Type::Void) {
                self.line("pure ()");
            } else {
                self.line("ub \"control reached the end of a function that returns a value\"");
            }
        }
        let body: Vec<String> = std::mem::take(&mut self.out)
            .iter()
            .flat_map(|l| l.lines())
            .map(str::to_owned)
            .collect();
        let mut lines = Vec::new();
        if self.frame_objs.is_empty() && prologue.is_empty() {
            // Written one level deeper, for the case below.
            lines.extend(
                body.iter()
                    .map(|l| l.strip_prefix("  ").unwrap_or(l).to_owned()),
            );
        } else {
            lines.extend(prologue.iter().map(|l| format!("  {l}")));
            for (p, size, align) in &self.frame_objs {
                lines.push(format!("  let {p} ← Mem.alloca {size} {align}"));
            }
            lines.push(format!("  let result : {ret} ← (do"));
            lines.extend(body);
            lines.push(format!("    : M {ret})"));
            if !self.frame_objs.is_empty() {
                let objs: Vec<&str> = self.frame_objs.iter().map(|o| o.0.as_str()).collect();
                lines.push(format!("  Mem.popFrame [{}]", objs.join(", ")));
            }
            lines.extend(epilogue.iter().map(|l| format!("  {l}")));
            lines.push("  pure result".to_owned());
        }
        let sig = Some(self.sig_of_fn(f));
        self.res.lines = lines;
        (self.res, params, sig)
    }

    /// The Lean shape of `f`, when all its types have one.
    pub(crate) fn signature(mut self, f: &Function) -> Option<Sig> {
        let sig = self.sig_of_fn(f);
        self.res.reasons.is_empty().then_some(sig)
    }

    fn sig_of_fn(&mut self, f: &Function) -> Sig {
        let params = f.params.iter().map(|p| self.lty(&p.ty)).collect();
        let ret = self.lty(&f.ret);
        Sig {
            params,
            variadic: f.variadic,
            ret,
        }
    }
}

fn elem_const(t: &QualType) -> bool {
    match &t.ty {
        Type::Array { elem, .. } => elem.quals.is_const || elem_const(elem),
        _ => false,
    }
}

/// Whether `f` invokes `va_start`, `va_copy` or `va_end`, which clang
/// gives as calls of builtins.
fn uses_va_macros(f: &Function) -> bool {
    let mut found = false;
    crate::emit::order::for_each_expr(&f.body, &mut |e| {
        if let crate::ir::ExprKind::Call {
            direct: Some(name), ..
        } = &e.kind
        {
            found |= matches!(
                name.as_str(),
                "__builtin_va_start" | "__builtin_va_end" | "__builtin_va_copy"
            );
        }
    });
    found
}
