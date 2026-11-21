//! Turns clang's JSON nodes into the IR.

use std::collections::{BTreeSet, HashMap};

use serde_json::Value;

use crate::clang::{FnDeclInfo, RawTu, node_loc, range_lines};
use crate::ir::{
    BinOp, CastKind, Decl, EnumDef, Expr, ExprKind, Field, Function, Global, Linkage, LocalVar,
    LogicalOp, Origin, Param, RecordDef, Stmt, Storage, TraitArg, TypeTrait, UnaryOp, Unsupported,
    VarRef,
};
use crate::types::{IntType, QualType, RecordKind, TagKind, TagName, Type, TypeCtx};

pub(crate) fn kind(v: &Value) -> &str {
    v.get("kind").and_then(Value::as_str).unwrap_or("")
}

pub(crate) fn inner(v: &Value) -> &[Value] {
    v.get("inner")
        .and_then(Value::as_array)
        .map_or(&[], Vec::as_slice)
}

pub(crate) fn text<'a>(v: &'a Value, key: &str) -> Option<&'a str> {
    v.get(key).and_then(Value::as_str)
}

fn flag(v: &Value, key: &str) -> bool {
    v.get(key).and_then(Value::as_bool).unwrap_or(false)
}

fn is_attr(v: &Value) -> bool {
    kind(v).ends_with("Attr")
}

fn attr_names(v: &Value) -> Vec<String> {
    inner(v)
        .iter()
        .filter(|c| is_attr(c))
        .map(|c| kind(c).trim_end_matches("Attr").to_owned())
        .collect()
}

const COMMON_KEYS: &[&str] = &[
    "id",
    "kind",
    "loc",
    "range",
    "inner",
    "type",
    "valueCategory",
];

/// The keys the converter understands on each node kind it converts. A key
/// outside this list may carry meaning, so the node is reported instead of
/// being converted without it.
fn known_keys(kind: &str) -> Option<&'static [&'static str]> {
    Some(match kind {
        "CompoundStmt"
        | "DeclStmt"
        | "NullStmt"
        | "ReturnStmt"
        | "BreakStmt"
        | "ContinueStmt"
        | "DoStmt"
        | "ForStmt"
        | "DefaultStmt"
        | "AttributedStmt"
        | "ParenExpr"
        | "CallExpr"
        | "ConditionalOperator"
        | "ArraySubscriptExpr"
        | "CompoundLiteralExpr"
        | "ImplicitValueInitExpr" => &[],
        "CaseStmt" => &["isGNURange"],
        "SwitchStmt" => &["hasInit", "hasVar"],
        "WhileStmt" => &["hasVar"],
        "IfStmt" => &["hasElse", "hasInit", "hasVar"],
        "LabelStmt" => &["declId", "name"],
        "GotoStmt" => &["targetLabelDeclId"],
        "ConstantExpr" | "IntegerLiteral" | "CharacterLiteral" | "FloatingLiteral"
        | "StringLiteral" => &["value"],
        "PredefinedExpr" | "AtomicExpr" => &["name"],
        "DeclRefExpr" => &["referencedDecl", "nonOdrUseReason"],
        "ImplicitCastExpr" => &["castKind", "isPartOfExplicitCast"],
        "CStyleCastExpr" => &["castKind"],
        "UnaryOperator" => &["opcode", "isPostfix", "canOverflow"],
        "BinaryOperator" => &["opcode"],
        "CompoundAssignOperator" => &["opcode", "computeLHSType", "computeResultType"],
        "MemberExpr" => &["name", "isArrow", "referencedMemberDecl", "nonOdrUseReason"],
        "UnaryExprOrTypeTraitExpr" => &["name", "argType"],
        "InitListExpr" => &["array_filler", "field"],
        "VarDecl" => &[
            "name",
            "init",
            "isUsed",
            "isReferenced",
            "storageClass",
            "nrvo",
            "mangledName",
            "tls",
        ],
        _ => return None,
    })
}

fn unknown_key(v: &Value) -> Option<String> {
    let known = known_keys(kind(v))?;
    v.as_object()?
        .keys()
        .find(|k| !COMMON_KEYS.contains(&k.as_str()) && !known.contains(&k.as_str()))
        .cloned()
}

fn loc_string(v: &Value) -> Option<String> {
    node_loc(v).map(|l| l.to_string())
}

/// Parses the spelling of a `type` object, falling back to clang's
/// desugared spelling when the sugared one cannot be read.
pub(crate) fn type_of(types: &mut TypeCtx, t: Option<&Value>) -> QualType {
    let Some(t) = t else {
        return QualType::unsupported("", "node has no type");
    };
    let q = text(t, "qualType").unwrap_or("");
    let first = types.parse(q);
    if matches!(first.ty, Type::Unsupported { .. })
        && let Some(d) = text(t, "desugaredQualType")
    {
        let second = types.parse(d);
        if !matches!(second.ty, Type::Unsupported { .. }) {
            return second;
        }
    }
    first
}

#[derive(Debug)]
struct RawTag<'r> {
    node: &'r Value,
    complete: bool,
}

/// Translation-unit-wide tables, built before any function is converted.
#[derive(Debug)]
pub(crate) struct Unit<'r> {
    pub(crate) types: TypeCtx,
    records: HashMap<(RecordKind, TagName), RawTag<'r>>,
    enums: HashMap<TagName, RawTag<'r>>,
    enum_consts: HashMap<String, (String, Result<i128, String>)>,
    globals: HashMap<String, &'r Value>,
    globals_by_name: HashMap<String, Vec<&'r Value>>,
    fn_decls: &'r HashMap<String, FnDeclInfo>,
    /// Results of the clang probes, keyed by the C expression probed.
    pub(crate) probes: HashMap<String, Result<u64, String>>,
}

fn tag_kind(keyword: &str) -> Option<TagKind> {
    TagKind::from_keyword(keyword)
}

impl<'r> Unit<'r> {
    pub(crate) fn new(types: TypeCtx, raw: &'r RawTu) -> Self {
        let mut u = Self {
            types,
            records: HashMap::new(),
            enums: HashMap::new(),
            enum_consts: HashMap::new(),
            globals: HashMap::new(),
            globals_by_name: HashMap::new(),
            fn_decls: &raw.fn_decls,
            probes: HashMap::new(),
        };
        let mut typedef_owned: HashMap<String, String> = HashMap::new();
        for d in &raw.decls {
            if kind(d) != "TypedefDecl" {
                continue;
            }
            let (Some(name), Some(spelling)) = (
                text(d, "name"),
                d.get("type").and_then(|t| text(t, "qualType")),
            ) else {
                continue;
            };
            u.types.add_typedef(name, spelling);
            for c in inner(d) {
                let Some(owned) = c.get("ownedTagDecl") else {
                    continue;
                };
                if text(owned, "name").unwrap_or("").is_empty()
                    && let (Some(id), Some(kw)) = (text(owned, "id"), spelling.split(' ').next())
                {
                    typedef_owned.insert(id.to_owned(), name.to_owned());
                    if let Some(k) = tag_kind(kw) {
                        u.types.add_typedef_tag(k, name);
                    }
                }
            }
        }
        for d in &raw.decls {
            u.index_decl(d, &typedef_owned);
        }
        u
    }

    fn tag_key(
        &mut self,
        d: &Value,
        k: TagKind,
        owned: &HashMap<String, String>,
    ) -> Option<TagName> {
        match text(d, "name").filter(|n| !n.is_empty()) {
            Some(n) => {
                self.types.add_tag(k, n);
                Some(TagName::Tag(n.to_owned()))
            }
            None => text(d, "id").and_then(|id| owned.get(id)).map_or_else(
                || loc_string(d).map(TagName::Anon),
                |t| Some(TagName::Typedef(t.clone())),
            ),
        }
    }

    fn index_decl(&mut self, d: &'r Value, owned: &HashMap<String, String>) {
        match kind(d) {
            "RecordDecl" => {
                let k = match text(d, "tagUsed") {
                    Some("union") => RecordKind::Union,
                    _ => RecordKind::Struct,
                };
                let tk = if k == RecordKind::Union {
                    TagKind::Union
                } else {
                    TagKind::Struct
                };
                if let Some(name) = self.tag_key(d, tk, owned) {
                    let complete = flag(d, "completeDefinition");
                    let e = self
                        .records
                        .entry((k, name))
                        .or_insert(RawTag { node: d, complete });
                    if complete && !e.complete {
                        *e = RawTag { node: d, complete };
                    }
                }
                for c in inner(d) {
                    self.index_decl(c, owned);
                }
            }
            "EnumDecl" => {
                if let Some(name) = self.tag_key(d, TagKind::Enum, owned) {
                    let complete = !inner(d).is_empty();
                    let e = self
                        .enums
                        .entry(name)
                        .or_insert(RawTag { node: d, complete });
                    if complete && !e.complete {
                        *e = RawTag { node: d, complete };
                    }
                }
                self.index_enum_consts(d);
            }
            "VarDecl" => {
                if let Some(id) = text(d, "id") {
                    self.globals.insert(id.to_owned(), d);
                }
                if let Some(n) = text(d, "name") {
                    self.globals_by_name
                        .entry(n.to_owned())
                        .or_default()
                        .push(d);
                }
            }
            _ => {}
        }
    }

    fn index_enum_consts(&mut self, d: &Value) {
        let mut next: Result<i128, String> = Ok(0);
        for c in inner(d).iter().filter(|c| kind(c) == "EnumConstantDecl") {
            let name = text(c, "name").unwrap_or("").to_owned();
            let value = inner(c).first().map_or_else(
                || next.clone(),
                |init| {
                    text(init, "value")
                        .and_then(|t| t.parse::<i128>().ok())
                        .ok_or_else(|| format!("clang gave no value for enumerator `{name}`"))
                },
            );
            next = value.as_ref().map(|v| v + 1).map_err(Clone::clone);
            if let Some(id) = text(c, "id") {
                self.enum_consts.insert(id.to_owned(), (name, value));
            }
        }
    }

    /// Enums whose compatible integer type the probes should ask for.
    pub(crate) fn probe_enums(&self) -> Vec<TagName> {
        let mut v: Vec<TagName> = self
            .enums
            .iter()
            .filter(|(n, t)| t.complete && !matches!(n, TagName::Anon(_)))
            .map(|(n, _)| n.clone())
            .collect();
        v.sort();
        v
    }

    fn linkage(&self, id: Option<&str>, node: &Value) -> Linkage {
        let mut is_static = text(node, "storageClass") == Some("static");
        let mut cur = text(node, "previousDecl").map(String::from);
        let mut steps = 0;
        // `steps` guards against a cycle in clang's redeclaration chain.
        while let Some(info) = cur.as_deref().and_then(|p| self.fn_decls.get(p)) {
            is_static |= info.is_static;
            if steps > 1000 || info.previous.as_deref() == id {
                break;
            }
            cur.clone_from(&info.previous);
            steps += 1;
        }
        if is_static {
            Linkage::Internal
        } else {
            Linkage::External
        }
    }

    pub(crate) fn function(&mut self, v: &Value, origin: Origin, def_file: String) -> Function {
        let mut fx = FnCx::new(self);
        fx.collect_labels(v);
        let fty = type_of(&mut fx.unit.types, v.get("type"));
        let (ret, noreturn_ty) = match &fty.ty {
            Type::Function(ft) => (ft.ret.clone(), ft.noreturn),
            _ => (
                QualType::unsupported("", "function without a function type"),
                false,
            ),
        };
        let mut params = Vec::new();
        for p in inner(v).iter().filter(|c| kind(c) == "ParmVarDecl") {
            let name = text(p, "name").unwrap_or("").to_owned();
            if let Some(id) = text(p, "id") {
                fx.params
                    .insert(id.to_owned(), (params.len(), name.clone()));
            }
            params.push(Param {
                name,
                ty: type_of(&mut fx.unit.types, p.get("type")),
            });
        }
        let body = inner(v)
            .iter()
            .find(|c| kind(c) == "CompoundStmt")
            .map_or(Stmt::Null, |b| fx.stmt(b));
        let attrs = attr_names(v);
        let noreturn = noreturn_ty || attrs.iter().any(|a| a == "NoReturn" || a == "C11NoReturn");
        let lines = range_lines(v).map_or(0, |(a, b)| b.saturating_sub(a) + 1);
        Function {
            name: text(v, "name").unwrap_or("").to_owned(),
            origin,
            def_file,
            linkage: fx.unit.linkage(text(v, "id"), v),
            inline: flag(v, "inline"),
            params,
            ret,
            variadic: flag(v, "variadic"),
            noreturn,
            attrs,
            body,
            globals: std::mem::take(&mut fx.globals).into_iter().collect(),
            loc: node_loc(v),
            lines,
        }
    }

    pub(crate) fn record_def(&mut self, key: &(RecordKind, TagName)) -> RecordDef {
        let node = self.records.get(key).filter(|t| t.complete).map(|t| t.node);
        let fields = node.map(|n| {
            inner(n)
                .iter()
                .filter(|c| kind(c) == "FieldDecl")
                .map(|c| Field {
                    name: text(c, "name").unwrap_or("").to_owned(),
                    ty: type_of(&mut self.types, c.get("type")),
                    bit_width: if flag(c, "isBitfield") {
                        inner(c)
                            .first()
                            .and_then(|w| text(w, "value"))
                            .and_then(|w| w.parse().ok())
                    } else {
                        None
                    },
                })
                .collect()
        });
        RecordDef {
            kind: key.0,
            name: key.1.clone(),
            fields,
            attrs: node.map(attr_names).unwrap_or_default(),
        }
    }

    pub(crate) fn enum_def(&self, name: &TagName, underlying: Result<IntType, String>) -> EnumDef {
        let constants = self
            .enums
            .get(name)
            .map(|t| {
                inner(t.node)
                    .iter()
                    .filter_map(|c| text(c, "id"))
                    .filter_map(|id| self.enum_consts.get(id))
                    .filter_map(|(n, v)| v.as_ref().ok().map(|v| (n.clone(), *v)))
                    .collect()
            })
            .unwrap_or_default();
        EnumDef {
            name: name.clone(),
            underlying,
            constants,
        }
    }

    pub(crate) fn global(&mut self, name: &str, main: &dyn Fn(&str) -> bool) -> Option<Global> {
        let decls = self.globals_by_name.get(name)?.clone();
        let def = decls
            .iter()
            .rev()
            .find(|d| text(d, "init").is_some())
            .or_else(|| decls.last())?;
        let storages: Vec<Option<&str>> = decls.iter().map(|d| text(d, "storageClass")).collect();
        let storage = if storages.contains(&Some("static")) {
            Storage::Static
        } else if storages.iter().all(|s| *s == Some("extern")) {
            Storage::Extern
        } else {
            Storage::None
        };
        let ty = type_of(&mut self.types, def.get("type"));
        let in_main_file = node_loc(def).is_some_and(|l| main(&l.file));
        let init = if text(def, "init").is_some() {
            let mut fx = FnCx::new(self);
            inner(def).iter().find(|c| !is_attr(c)).map(|e| fx.expr(e))
        } else {
            None
        };
        Some(Global {
            name: name.to_owned(),
            ty,
            storage,
            init,
            in_main_file,
        })
    }
}

/// State for converting one function body.
struct FnCx<'u, 'r> {
    unit: &'u mut Unit<'r>,
    params: HashMap<String, (usize, String)>,
    locals: HashMap<String, (u32, String)>,
    next_local: u32,
    labels: HashMap<String, String>,
    globals: BTreeSet<String>,
}

fn unsupported(v: &Value, reason: impl Into<String>) -> Unsupported {
    Unsupported {
        clang_kind: kind(v).to_owned(),
        reason: reason.into(),
        loc: node_loc(v),
    }
}

fn bin_op(op: &str) -> Option<BinOp> {
    Some(match op {
        "*" => BinOp::Mul,
        "/" => BinOp::Div,
        "%" => BinOp::Rem,
        "+" => BinOp::Add,
        "-" => BinOp::Sub,
        "<<" => BinOp::Shl,
        ">>" => BinOp::Shr,
        "<" => BinOp::Lt,
        ">" => BinOp::Gt,
        "<=" => BinOp::Le,
        ">=" => BinOp::Ge,
        "==" => BinOp::Eq,
        "!=" => BinOp::Ne,
        "&" => BinOp::BitAnd,
        "^" => BinOp::BitXor,
        "|" => BinOp::BitOr,
        _ => return None,
    })
}

impl<'u, 'r> FnCx<'u, 'r> {
    fn new(unit: &'u mut Unit<'r>) -> Self {
        Self {
            unit,
            params: HashMap::new(),
            locals: HashMap::new(),
            next_local: 1,
            labels: HashMap::new(),
            globals: BTreeSet::new(),
        }
    }

    fn collect_labels(&mut self, v: &Value) {
        if kind(v) == "LabelStmt"
            && let (Some(id), Some(name)) = (text(v, "declId"), text(v, "name"))
        {
            self.labels.insert(id.to_owned(), name.to_owned());
        }
        for c in inner(v) {
            self.collect_labels(c);
        }
    }

    fn ty(&mut self, v: &Value) -> QualType {
        type_of(&mut self.unit.types, v.get("type"))
    }

    fn opt_stmt(&mut self, v: Option<&Value>) -> Option<Stmt> {
        v.filter(|c| !kind(c).is_empty()).map(|c| self.stmt(c))
    }

    fn opt_expr(&mut self, v: Option<&Value>) -> Option<Expr> {
        v.filter(|c| !kind(c).is_empty()).map(|c| self.expr(c))
    }

    fn sub_stmt(&mut self, v: &Value, i: usize) -> Box<Stmt> {
        Box::new(inner(v).get(i).map_or_else(
            || Stmt::Unsupported(unsupported(v, "missing sub-statement")),
            |c| self.stmt(c),
        ))
    }

    fn sub_expr(&mut self, v: &Value, i: usize) -> Expr {
        match inner(v).get(i) {
            Some(c) => self.expr(c),
            None => self.unsup_expr(v, "missing operand"),
        }
    }

    fn stmt(&mut self, v: &Value) -> Stmt {
        if v.get("valueCategory").is_some() {
            return Stmt::Expr(self.expr(v));
        }
        if let Some(k) = unknown_key(v) {
            return Stmt::Unsupported(unsupported(
                v,
                format!("clang attribute `{k}` is not understood"),
            ));
        }
        let ch = inner(v);
        match kind(v) {
            "CompoundStmt" => Stmt::Compound(ch.iter().map(|c| self.stmt(c)).collect()),
            "DeclStmt" => Stmt::Decl(ch.iter().map(|c| self.decl(c)).collect()),
            "NullStmt" => Stmt::Null,
            "ReturnStmt" => Stmt::Return(self.opt_expr(ch.first())),
            "BreakStmt" => Stmt::Break,
            "ContinueStmt" => Stmt::Continue,
            "IfStmt" | "SwitchStmt" | "WhileStmt" | "DoStmt" | "ForStmt" | "CaseStmt"
            | "DefaultStmt" => self.control(v),
            "LabelStmt" => Stmt::Label {
                name: text(v, "name").unwrap_or("").to_owned(),
                body: self.sub_stmt(v, 0),
            },
            "GotoStmt" => text(v, "targetLabelDeclId")
                .and_then(|id| self.labels.get(id))
                .map_or_else(
                    || {
                        Stmt::Unsupported(unsupported(
                            v,
                            "goto to a label not found in the function",
                        ))
                    },
                    |l| Stmt::Goto(l.clone()),
                ),
            "AttributedStmt" => {
                let attrs = attr_names(v);
                if attrs.iter().all(|a| a == "FallThrough") {
                    ch.iter()
                        .find(|c| !is_attr(c))
                        .map_or(Stmt::Null, |s| self.stmt(s))
                } else {
                    Stmt::Unsupported(unsupported(v, format!("statement attributes {attrs:?}")))
                }
            }
            "GCCAsmStmt" | "MSAsmStmt" => Stmt::Unsupported(unsupported(v, "inline assembly")),
            "IndirectGotoStmt" => Stmt::Unsupported(unsupported(v, "computed goto (`goto *p`)")),
            k => Stmt::Unsupported(unsupported(
                v,
                format!("statement kind {k} is not represented"),
            )),
        }
    }

    /// Statements with sub-statements: branches, loops and switch labels.
    fn control(&mut self, v: &Value) -> Stmt {
        let ch = inner(v);
        match kind(v) {
            "IfStmt" | "SwitchStmt" | "WhileStmt" if flag(v, "hasInit") || flag(v, "hasVar") => {
                Stmt::Unsupported(unsupported(
                    v,
                    "condition with an init statement or variable",
                ))
            }
            "IfStmt" => {
                let cond = self.sub_expr(v, 0);
                let then = self.sub_stmt(v, 1);
                let els = if flag(v, "hasElse") {
                    Some(self.sub_stmt(v, 2))
                } else {
                    None
                };
                Stmt::If { cond, then, els }
            }
            "WhileStmt" => Stmt::While {
                cond: self.sub_expr(v, 0),
                body: self.sub_stmt(v, 1),
            },
            "DoStmt" => {
                let body = self.sub_stmt(v, 0);
                Stmt::DoWhile {
                    body,
                    cond: self.sub_expr(v, 1),
                }
            }
            "ForStmt" if ch.get(1).is_some_and(|c| !kind(c).is_empty()) => {
                Stmt::Unsupported(unsupported(v, "for with a condition variable"))
            }
            "ForStmt" => Stmt::For {
                init: self.opt_stmt(ch.first()).map(Box::new),
                cond: self.opt_expr(ch.get(2)).map(Box::new),
                inc: self.opt_expr(ch.get(3)).map(Box::new),
                body: self.sub_stmt(v, 4),
            },
            "SwitchStmt" => Stmt::Switch {
                cond: self.sub_expr(v, 0),
                body: self.sub_stmt(v, 1),
            },
            "CaseStmt" if flag(v, "isGNURange") => {
                Stmt::Unsupported(unsupported(v, "GNU case range `case a ... b`"))
            }
            "CaseStmt" => {
                let value = ch
                    .first()
                    .and_then(|c| text(c, "value"))
                    .and_then(|s| s.parse().ok());
                let expr = self.sub_expr(v, 0);
                Stmt::Case {
                    expr,
                    value,
                    body: self.sub_stmt(v, 1),
                }
            }
            "DefaultStmt" => Stmt::Default {
                body: self.sub_stmt(v, 0),
            },
            k => Stmt::Unsupported(unsupported(
                v,
                format!("statement kind {k} is not represented"),
            )),
        }
    }

    fn decl(&mut self, v: &Value) -> Decl {
        match kind(v) {
            "VarDecl" => self.local_var(v),
            "RecordDecl" | "EnumDecl" => Decl::Unsupported(unsupported(
                v,
                "struct, union or enum declared inside a function (its name would shadow file scope)",
            )),
            "TypedefDecl" => Decl::Unsupported(unsupported(v, "typedef inside a function")),
            "FunctionDecl" => {
                Decl::Unsupported(unsupported(v, "function declared inside a function"))
            }
            k => Decl::Unsupported(unsupported(
                v,
                format!("declaration kind {k} is not represented"),
            )),
        }
    }

    fn local_var(&mut self, v: &Value) -> Decl {
        const HARMLESS: &[&str] = &["Unused", "Used", "Aligned"];
        if let Some(k) = unknown_key(v) {
            return Decl::Unsupported(unsupported(
                v,
                format!("clang attribute `{k}` is not understood"),
            ));
        }
        let attrs = attr_names(v);
        if let Some(a) = attrs.iter().find(|a| !HARMLESS.contains(&a.as_str())) {
            return Decl::Unsupported(unsupported(v, format!("variable attribute `{a}`")));
        }
        let storage = match text(v, "storageClass") {
            None => Storage::None,
            Some("static") => Storage::Static,
            Some("register") => Storage::Register,
            Some(s) => {
                return Decl::Unsupported(unsupported(v, format!("block-scope `{s}` variable")));
            }
        };
        if flag(v, "tls") || text(v, "tls").is_some() {
            return Decl::Unsupported(unsupported(v, "thread-local variable"));
        }
        let name = text(v, "name").unwrap_or("").to_owned();
        let id = self.next_local;
        self.next_local += 1;
        if let Some(cid) = text(v, "id") {
            self.locals.insert(cid.to_owned(), (id, name.clone()));
        }
        let ty = self.ty(v);
        let init = if text(v, "init").is_some() {
            inner(v).iter().find(|c| !is_attr(c)).map(|c| self.expr(c))
        } else {
            None
        };
        Decl::Var(Box::new(LocalVar {
            id,
            name,
            ty,
            storage,
            init,
            attrs,
        }))
    }

    fn unsup_expr(&mut self, v: &Value, reason: impl Into<String>) -> Expr {
        let ty = self.ty(v);
        Expr {
            kind: ExprKind::Unsupported(unsupported(v, reason)),
            ty,
            lvalue: false,
            loc: node_loc(v),
        }
    }

    fn mk(&mut self, v: &Value, kind: ExprKind) -> Expr {
        let ty = self.ty(v);
        Expr {
            kind,
            ty,
            lvalue: text(v, "valueCategory") == Some("lvalue"),
            loc: node_loc(v),
        }
    }

    fn boxed(&mut self, v: &Value, i: usize) -> Box<Expr> {
        Box::new(self.sub_expr(v, i))
    }

    pub(crate) fn expr(&mut self, v: &Value) -> Expr {
        if let Some(k) = unknown_key(v) {
            return self.unsup_expr(v, format!("clang attribute `{k}` is not understood"));
        }
        match kind(v) {
            // Parentheses and constant-evaluation markers carry no meaning
            // of their own: clang has already applied them.
            "ParenExpr" | "ConstantExpr" => self.sub_expr(v, 0),
            "IntegerLiteral" | "CharacterLiteral" | "FloatingLiteral" | "StringLiteral"
            | "PredefinedExpr" | "DeclRefExpr" => self.leaf(v),
            "ImplicitCastExpr" | "CStyleCastExpr" => self.cast(v),
            "UnaryOperator" | "BinaryOperator" | "CompoundAssignOperator" => self.operator(v),
            _ => self.other(v),
        }
    }

    fn cast(&mut self, v: &Value) -> Expr {
        let ck = text(v, "castKind").unwrap_or("");
        match CastKind::from_clang(ck) {
            Some(k) => {
                let operand = self.boxed(v, 0);
                let explicit = kind(v) == "CStyleCastExpr";
                self.mk(
                    v,
                    ExprKind::Cast {
                        kind: k,
                        explicit,
                        operand,
                    },
                )
            }
            None => self.unsup_expr(v, format!("cast kind {ck}")),
        }
    }

    fn leaf(&mut self, v: &Value) -> Expr {
        match kind(v) {
            "IntegerLiteral" => match text(v, "value").map(str::parse::<u128>) {
                Some(Ok(n)) => self.mk(v, ExprKind::IntLit(n)),
                _ => self.unsup_expr(v, "integer literal without a readable value"),
            },
            "CharacterLiteral" => match v.get("value").and_then(Value::as_i64) {
                Some(c) => self.mk(v, ExprKind::CharLit(c)),
                None => self.unsup_expr(v, "character literal without a value"),
            },
            "FloatingLiteral" => self.float_lit(v),
            "StringLiteral" => self.string_lit(v),
            "PredefinedExpr" => {
                let name = text(v, "name").unwrap_or("").to_owned();
                let value = self.boxed(v, 0);
                self.mk(v, ExprKind::Predefined { name, value })
            }
            _ => self.decl_ref(v),
        }
    }

    fn float_lit(&mut self, v: &Value) -> Expr {
        let t = text(v, "value").unwrap_or("").to_owned();
        let ty = self.ty(v);
        let bits = match &ty.ty {
            Type::Float {
                kind: crate::types::FloatKind::Float,
                ..
            } => t.parse::<f32>().ok().map(|f| u64::from(f.to_bits())),
            Type::Float {
                kind: crate::types::FloatKind::Double,
                ..
            } => t.parse::<f64>().ok().map(f64::to_bits),
            _ => None,
        };
        match bits {
            Some(bits) => self.mk(v, ExprKind::FloatLit { text: t, bits }),
            None => self.unsup_expr(v, format!("floating literal `{t}` of type {ty}")),
        }
    }

    fn string_lit(&mut self, v: &Value) -> Expr {
        let raw = text(v, "value").unwrap_or("");
        let body = raw.strip_prefix("u8").unwrap_or(raw);
        if !body.starts_with('"') {
            return self.unsup_expr(v, "wide or UTF-16/32 string literal");
        }
        let ty = self.ty(v);
        let Some(bytes) = decode_c_string(body) else {
            return self.unsup_expr(v, format!("string literal {raw} could not be decoded"));
        };
        match &ty.ty {
            // A literal initializing a sized array takes that array's type:
            // `char b[7] = ""` gives `char[7]`, `char c[3] = "abc"` drops the NUL.
            Type::Array { len: Some(n), .. }
                if u64::try_from(bytes.len()).is_ok_and(|l| l <= *n) =>
            {
                self.mk(v, ExprKind::StringLit(bytes))
            }
            _ => self.unsup_expr(
                v,
                format!("string literal {raw} does not match its type {ty}"),
            ),
        }
    }

    fn decl_ref(&mut self, v: &Value) -> Expr {
        let Some(r) = v.get("referencedDecl") else {
            return self.unsup_expr(v, "reference without a declaration");
        };
        let id = text(r, "id").unwrap_or("");
        let name = text(r, "name").unwrap_or("").to_owned();
        match kind(r) {
            "ParmVarDecl" | "VarDecl" => {
                let var = if let Some((index, n)) = self.params.get(id) {
                    VarRef::Param {
                        index: *index,
                        name: n.clone(),
                    }
                } else if let Some((lid, n)) = self.locals.get(id) {
                    VarRef::Local {
                        id: *lid,
                        name: n.clone(),
                    }
                } else if self.unit.globals.contains_key(id) {
                    self.globals.insert(name.clone());
                    VarRef::Global { name }
                } else {
                    return self.unsup_expr(
                        v,
                        format!("reference to `{name}`, declared nowhere Achates saw"),
                    );
                };
                self.mk(v, ExprKind::Var(var))
            }
            "FunctionDecl" => {
                let builtin = text(v.get("type").unwrap_or(&Value::Null), "qualType")
                    == Some("<builtin fn type>");
                let mut e = self.mk(v, ExprKind::Func { name, builtin });
                if builtin {
                    // clang gives builtins a placeholder type; the
                    // declaration carries the real one.
                    e.ty = type_of(&mut self.unit.types, r.get("type"));
                }
                e
            }
            "EnumConstantDecl" => match self.unit.enum_consts.get(id).cloned() {
                Some((n, Ok(value))) => self.mk(v, ExprKind::EnumConst { name: n, value }),
                Some((_, Err(e))) => self.unsup_expr(v, e),
                None => self.unsup_expr(v, format!("enumerator `{name}` not found")),
            },
            k => self.unsup_expr(v, format!("reference to a {k}")),
        }
    }

    fn operator(&mut self, v: &Value) -> Expr {
        let op = text(v, "opcode").unwrap_or("");
        match kind(v) {
            "UnaryOperator" => {
                let post = flag(v, "isPostfix");
                let u = match (op, post) {
                    ("+", _) => UnaryOp::Plus,
                    ("-", _) => UnaryOp::Minus,
                    ("~", _) => UnaryOp::BitNot,
                    ("!", _) => UnaryOp::Not,
                    ("*", _) => UnaryOp::Deref,
                    ("&", _) => UnaryOp::AddrOf,
                    ("++", false) => UnaryOp::PreInc,
                    ("--", false) => UnaryOp::PreDec,
                    ("++", true) => UnaryOp::PostInc,
                    ("--", true) => UnaryOp::PostDec,
                    ("__extension__", _) => UnaryOp::Extension,
                    _ => return self.unsup_expr(v, format!("unary operator `{op}`")),
                };
                let operand = self.boxed(v, 0);
                self.mk(v, ExprKind::Unary { op: u, operand })
            }
            "CompoundAssignOperator" => {
                let Some(b) = op.strip_suffix('=').and_then(bin_op) else {
                    return self.unsup_expr(v, format!("compound assignment `{op}`"));
                };
                let compute_lhs = type_of(&mut self.unit.types, v.get("computeLHSType"));
                let compute_result = type_of(&mut self.unit.types, v.get("computeResultType"));
                let (lhs, rhs) = (self.boxed(v, 0), self.boxed(v, 1));
                self.mk(
                    v,
                    ExprKind::CompoundAssign {
                        op: b,
                        lhs,
                        rhs,
                        compute_lhs,
                        compute_result,
                    },
                )
            }
            _ => {
                let (lhs, rhs) = (self.boxed(v, 0), self.boxed(v, 1));
                let k = match op {
                    "&&" => ExprKind::Logical {
                        op: LogicalOp::And,
                        lhs,
                        rhs,
                    },
                    "||" => ExprKind::Logical {
                        op: LogicalOp::Or,
                        lhs,
                        rhs,
                    },
                    "," => ExprKind::Comma { lhs, rhs },
                    "=" => ExprKind::Assign { lhs, rhs },
                    _ => match bin_op(op) {
                        Some(b) => ExprKind::Binary { op: b, lhs, rhs },
                        None => return self.unsup_expr(v, format!("binary operator `{op}`")),
                    },
                };
                self.mk(v, k)
            }
        }
    }

    fn other(&mut self, v: &Value) -> Expr {
        let ch = inner(v);
        match kind(v) {
            "ConditionalOperator" => {
                let (cond, then, els) = (self.boxed(v, 0), self.boxed(v, 1), self.boxed(v, 2));
                self.mk(v, ExprKind::Cond { cond, then, els })
            }
            "CallExpr" => {
                let callee = self.boxed(v, 0);
                let args = ch.iter().skip(1).map(|a| self.expr(a)).collect();
                let direct = match &callee.kind {
                    ExprKind::Cast {
                        kind: CastKind::FunctionToPointerDecay | CastKind::BuiltinFnToFnPtr,
                        operand,
                        ..
                    } => match &operand.kind {
                        ExprKind::Func { name, .. } => Some(name.clone()),
                        _ => None,
                    },
                    _ => None,
                };
                self.mk(
                    v,
                    ExprKind::Call {
                        callee,
                        args,
                        direct,
                    },
                )
            }
            "MemberExpr" => {
                let base = self.boxed(v, 0);
                let field = text(v, "name").unwrap_or("").to_owned();
                self.mk(
                    v,
                    ExprKind::Member {
                        base,
                        field,
                        arrow: flag(v, "isArrow"),
                    },
                )
            }
            "ArraySubscriptExpr" => {
                let (lhs, rhs) = (self.boxed(v, 0), self.boxed(v, 1));
                self.mk(v, ExprKind::Index { lhs, rhs })
            }
            "UnaryExprOrTypeTraitExpr" => self.type_trait(v),
            "InitListExpr" => self.init_list(v),
            "CompoundLiteralExpr" => {
                let init = self.boxed(v, 0);
                self.mk(v, ExprKind::CompoundLiteral(init))
            }
            "ImplicitValueInitExpr" => self.mk(v, ExprKind::ImplicitValueInit),
            "AtomicExpr" => {
                let op = text(v, "name").unwrap_or("").to_owned();
                let operands = ch.iter().map(|a| self.expr(a)).collect();
                self.mk(v, ExprKind::Atomic { op, operands })
            }
            k => {
                let reason = match k {
                    "VAArgExpr" => "reading a variadic argument (`va_arg`)".to_owned(),
                    "StmtExpr" => "GNU statement expression `({ ... })`".to_owned(),
                    "BinaryConditionalOperator" => "GNU `a ?: b`".to_owned(),
                    "GenericSelectionExpr" => "`_Generic` selection".to_owned(),
                    "OffsetOfExpr" => "`offsetof` (clang does not print its value)".to_owned(),
                    "AddrLabelExpr" => "address of a label (`&&label`)".to_owned(),
                    "ChooseExpr" => "`__builtin_choose_expr`".to_owned(),
                    _ => format!("expression kind {k} is not represented"),
                };
                self.unsup_expr(v, reason)
            }
        }
    }

    fn init_list(&mut self, v: &Value) -> Expr {
        let union_field = v
            .get("field")
            .and_then(|f| text(f, "name"))
            .map(String::from);
        // clang prints the elements of a list with a filler inside the
        // `array_filler` array, after the filler itself.
        let (filler, elems) = match v.get("array_filler").and_then(Value::as_array) {
            Some(a) => {
                let mut it = a.iter();
                let filler = it.next().map(|f| Box::new(self.expr(f)));
                (filler, it.map(|e| self.expr(e)).collect())
            }
            None => (None, inner(v).iter().map(|e| self.expr(e)).collect()),
        };
        self.mk(
            v,
            ExprKind::InitList {
                elems,
                filler,
                union_field,
            },
        )
    }

    fn type_trait(&mut self, v: &Value) -> Expr {
        let trait_ = match text(v, "name") {
            Some("sizeof") => TypeTrait::Size,
            Some("alignof") => TypeTrait::Align,
            Some("__alignof") => TypeTrait::PreferredAlign,
            other => return self.unsup_expr(v, format!("type trait {other:?}")),
        };
        let (arg, measured) = if let Some(t) = v.get("argType") {
            let q = type_of(&mut self.unit.types, Some(t));
            (TraitArg::Type(q.clone()), q)
        } else {
            let e = self.sub_expr(v, 0);
            let q = e.ty.clone();
            (TraitArg::Expr(Box::new(e)), q)
        };
        match probe_key(trait_, &measured).map(|k| self.unit.probes.get(&k).cloned()) {
            Some(Some(Ok(value))) => self.mk(v, ExprKind::TypeTrait { trait_, arg, value }),
            Some(Some(Err(e))) => self.unsup_expr(v, format!("clang could not evaluate it: {e}")),
            Some(None) => self.unsup_expr(v, "no probe was made for it (Achates bug)"),
            None => self.unsup_expr(v, format!("operand type {measured} cannot be named at file scope, so its value cannot be asked of clang")),
        }
    }
}

/// The C expression a probe evaluates for a type trait.
pub(crate) fn probe_key(t: TypeTrait, ty: &QualType) -> Option<String> {
    let c = crate::types::to_c(ty)?;
    Some(match t {
        TypeTrait::Size => format!("sizeof({c})"),
        TypeTrait::Align => format!("_Alignof({c})"),
        TypeTrait::PreferredAlign => format!("__alignof__({c})"),
    })
}

/// Decodes a C string literal as clang prints it, quotes included.
pub(crate) fn decode_c_string(s: &str) -> Option<Vec<u8>> {
    let body = s.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = Vec::new();
    let b = body.as_bytes();
    let mut i = 0;
    while let Some(&c) = b.get(i) {
        i += 1;
        if c != b'\\' {
            out.push(c);
            continue;
        }
        let e = *b.get(i)?;
        i += 1;
        let simple = match e {
            b'n' => Some(b'\n'),
            b't' => Some(b'\t'),
            b'r' => Some(b'\r'),
            b'a' => Some(0x07),
            b'b' => Some(0x08),
            b'f' => Some(0x0c),
            b'v' => Some(0x0b),
            b'e' => Some(0x1b),
            b'\\' | b'\'' | b'"' | b'?' => Some(e),
            _ => None,
        };
        if let Some(x) = simple {
            out.push(x);
        } else if e == b'x' {
            let start = i;
            while b.get(i).is_some_and(u8::is_ascii_hexdigit) {
                i += 1;
            }
            let digits = std::str::from_utf8(b.get(start..i)?).ok()?;
            out.push(u8::try_from(u32::from_str_radix(digits, 16).ok()?).ok()?);
        } else if (b'0'..=b'7').contains(&e) {
            let start = i - 1;
            while i < start + 3 && b.get(i).is_some_and(|d| (b'0'..=b'7').contains(d)) {
                i += 1;
            }
            let digits = std::str::from_utf8(b.get(start..i)?).ok()?;
            out.push(u8::try_from(u32::from_str_radix(digits, 8).ok()?).ok()?);
        } else {
            return None;
        }
    }
    Some(out)
}

/// The record and enum names a type mentions, without looking inside
/// records.
pub(crate) fn tags_in(
    t: &QualType,
    records: &mut BTreeSet<(RecordKind, TagName)>,
    enums: &mut BTreeSet<TagName>,
) {
    crate::types::walk(t, &mut |q| match &q.ty {
        Type::Record { kind, name } => {
            records.insert((*kind, name.clone()));
        }
        Type::Enum(n) => {
            enums.insert(n.clone());
        }
        _ => {}
    });
}

/// Names of the functions `v` refers to, called or with their address taken.
pub(crate) fn raw_function_refs(v: &Value, out: &mut BTreeSet<String>) {
    if kind(v) == "DeclRefExpr"
        && let Some(r) = v.get("referencedDecl")
        && kind(r) == "FunctionDecl"
        && let Some(n) = text(r, "name")
    {
        out.insert(n.to_owned());
    }
    for c in inner(v) {
        raw_function_refs(c, out);
    }
    if let Some(a) = v.get("array_filler").and_then(Value::as_array) {
        for c in a {
            raw_function_refs(c, out);
        }
    }
}
