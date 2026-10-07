//! The lean4export 3.1.0 NDJSON format.

use crate::{
    env::{Binder, Hints, QuotKind},
    error::{corrupt, Result},
    record::{
        Binding, Counts, Decl, Head, IndCtor, IndRec, IndRule, IndType, Record, Safety, Sink,
    },
};
use serde::Deserialize;
use serde_json::value::RawValue;
use std::io::{BufRead, Write};

/// Writes records as NDJSON lines, byte for byte as lean4export does.
#[derive(Debug)]
pub struct Ndjson<W: Write> {
    out: W,
    buf: Vec<u8>,
    next: Counts,
}

impl<W: Write> Ndjson<W> {
    pub const fn new(out: W) -> Self {
        Self {
            out,
            buf: Vec::new(),
            next: Counts {
                names: 1,
                levels: 1,
                exprs: 0,
            },
        }
    }

    fn start(&mut self) -> &mut Self {
        self.buf.clear();
        self
    }

    fn emit(&mut self) -> Result<()> {
        self.buf.push(b'\n');
        self.out.write_all(&self.buf)?;
        Ok(())
    }

    fn s(&mut self, s: &str) -> &mut Self {
        self.buf.extend_from_slice(s.as_bytes());
        self
    }

    fn n(&mut self, n: impl itoa::Integer) -> &mut Self {
        self.s(itoa::Buffer::new().format(n))
    }

    fn b(&mut self, b: bool) -> &mut Self {
        self.s(if b { "true" } else { "false" })
    }

    fn list(&mut self, ids: &[u32]) -> &mut Self {
        self.s("[");
        for (i, &id) in ids.iter().enumerate() {
            if i > 0 {
                self.s(",");
            }
            self.n(id);
        }
        self.s("]")
    }

    fn q(&mut self, s: &str) -> &mut Self {
        self.s("\"");
        for c in s.chars() {
            match c {
                '"' => self.s("\\\""),
                '\\' => self.s("\\\\"),
                '\n' => self.s("\\n"),
                '\r' => self.s("\\r"),
                '\t' => self.s("\\t"),
                c if (c as u32) < 0x20 || c == '\u{7f}' => {
                    self.s("\\u00").s(&format!("{:02x}", c as u32))
                }
                c => self.s(c.encode_utf8(&mut [0; 4])),
            };
        }
        self.s("\"")
    }

    /// `"levelParams":[..],"name":N` and, for `ty`, `"type":T`.
    fn lp_name(&mut self, h: &Head) -> &mut Self {
        self.s(r#""levelParams":"#)
            .list(&h.level_params)
            .s(r#","name":"#)
            .n(h.name)
    }

    fn unsafe_(&mut self, u: bool) -> &mut Self {
        self.s(r#""isUnsafe":"#).b(u)
    }

    fn ctor(&mut self, c: &IndCtor) {
        self.s(r#"{"cidx":"#)
            .n(c.cidx)
            .s(r#","induct":"#)
            .n(c.induct)
            .s(",")
            .unsafe_(c.is_unsafe)
            .s(",")
            .lp_name(&c.head)
            .s(r#","numFields":"#)
            .n(c.num_fields)
            .s(r#","numParams":"#)
            .n(c.num_params)
            .s(r#","type":"#)
            .n(c.head.ty)
            .s("}");
    }

    fn rec(&mut self, r: &IndRec) {
        self.s(r#"{"all":"#)
            .list(&r.all)
            .s(",")
            .unsafe_(r.is_unsafe)
            .s(r#","k":"#)
            .b(r.k)
            .s(",")
            .lp_name(&r.head)
            .s(r#","numIndices":"#)
            .n(r.num_indices)
            .s(r#","numMinors":"#)
            .n(r.num_minors)
            .s(r#","numMotives":"#)
            .n(r.num_motives)
            .s(r#","numParams":"#)
            .n(r.num_params)
            .s(r#","rules":["#);
        for (i, rule) in r.rules.iter().enumerate() {
            if i > 0 {
                self.s(",");
            }
            self.s(r#"{"ctor":"#)
                .n(rule.ctor)
                .s(r#","nfields":"#)
                .n(rule.nfields)
                .s(r#","rhs":"#)
                .n(rule.rhs)
                .s("}");
        }
        self.s(r#"],"type":"#).n(r.head.ty).s("}");
    }

    fn ty(&mut self, t: &IndType) {
        self.s(r#"{"all":"#)
            .list(&t.all)
            .s(r#","ctors":"#)
            .list(&t.ctors)
            .s(r#","isRec":"#)
            .b(t.is_rec)
            .s(r#","isReflexive":"#)
            .b(t.is_reflexive)
            .s(",")
            .unsafe_(t.is_unsafe)
            .s(",")
            .lp_name(&t.head)
            .s(r#","numIndices":"#)
            .n(t.num_indices)
            .s(r#","numNested":"#)
            .n(t.num_nested)
            .s(r#","numParams":"#)
            .n(t.num_params)
            .s(r#","type":"#)
            .n(t.head.ty)
            .s("}");
    }

    fn all_opt(&mut self, all: Option<&Vec<u32>>) -> &mut Self {
        if let Some(all) = all {
            self.s(r#""all":"#).list(all).s(",");
        }
        self
    }
}

const fn binder(b: Binder) -> &'static str {
    match b {
        Binder::Default => "default",
        Binder::Implicit => "implicit",
        Binder::StrictImplicit => "strictImplicit",
        Binder::InstImplicit => "instImplicit",
    }
}

impl<W: Write> Sink for Ndjson<W> {
    type Output = W;

    fn record(&mut self, r: &Record<'_>) -> Result<()> {
        let Some(id) = self.next.assign(r) else {
            self.start();
            match r {
                Record::Meta(json) => {
                    self.start().s(r#"{"meta":"#).s(json).s("}");
                }
                Record::Decl(d) => self.decl(d),
                _ => return Ok(()),
            }
            return self.emit();
        };
        self.start();
        let level = |this: &mut Self, key: &str| {
            this.s(r#"{"il":"#).n(id).s(r#",""#).s(key).s(r#"":"#);
        };
        let binding = |this: &mut Self, b: &Binding| {
            this.s(r#"{"binderInfo":""#)
                .s(binder(b.info))
                .s(r#"","body":"#)
                .n(b.body)
                .s(r#","name":"#)
                .n(b.name)
                .s(r#","type":"#)
                .n(b.ty)
                .s("}");
        };
        match r {
            Record::NameStr { pre, str } => {
                self.s(r#"{"in":"#)
                    .n(id)
                    .s(r#","str":{"pre":"#)
                    .n(*pre)
                    .s(r#","str":"#)
                    .q(str)
                    .s("}}");
            }
            Record::NameNum { pre, i } => {
                self.s(r#"{"in":"#)
                    .n(id)
                    .s(r#","num":{"i":"#)
                    .n(*i)
                    .s(r#","pre":"#)
                    .n(*pre)
                    .s("}}");
            }
            Record::Succ(a) => {
                level(self, "succ");
                self.n(*a).s("}");
            }
            Record::Param(a) => {
                level(self, "param");
                self.n(*a).s("}");
            }
            Record::Max(a, b) | Record::IMax(a, b) => {
                level(
                    self,
                    if matches!(r, Record::Max(..)) {
                        "max"
                    } else {
                        "imax"
                    },
                );
                self.s("[").n(*a).s(",").n(*b).s("]}");
            }
            Record::BVar(i) => {
                self.s(r#"{"bvar":"#).n(*i).s(r#","ie":"#).n(id).s("}");
            }
            Record::Sort(l) => {
                self.s(r#"{"ie":"#).n(id).s(r#","sort":"#).n(*l).s("}");
            }
            Record::Const { name, us } => {
                self.s(r#"{"const":{"name":"#)
                    .n(*name)
                    .s(r#","us":"#)
                    .list(us)
                    .s(r#"},"ie":"#)
                    .n(id)
                    .s("}");
            }
            Record::App { fun, arg } => {
                self.s(r#"{"app":{"arg":"#)
                    .n(*arg)
                    .s(r#","fn":"#)
                    .n(*fun)
                    .s(r#"},"ie":"#)
                    .n(id)
                    .s("}");
            }
            Record::Lam(b) => {
                self.s(r#"{"ie":"#).n(id).s(r#","lam":"#);
                binding(self, b);
                self.s("}");
            }
            Record::Pi(b) => {
                self.s(r#"{"forallE":"#);
                binding(self, b);
                self.s(r#","ie":"#).n(id).s("}");
            }
            Record::Let {
                name,
                ty,
                value,
                body,
                nondep,
            } => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","letE":{"body":"#)
                    .n(*body)
                    .s(r#","name":"#)
                    .n(*name)
                    .s(r#","nondep":"#)
                    .b(*nondep)
                    .s(r#","type":"#)
                    .n(*ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Record::Nat(v) => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","natVal":""#)
                    .s(v)
                    .s(r#""}"#);
            }
            Record::Str(v) => {
                self.s(r#"{"ie":"#).n(id).s(r#","strVal":"#).q(v).s("}");
            }
            Record::Proj {
                type_name,
                idx,
                struct_,
            } => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","proj":{"idx":"#)
                    .n(*idx)
                    .s(r#","struct":"#)
                    .n(*struct_)
                    .s(r#","typeName":"#)
                    .n(*type_name)
                    .s("}}");
            }
            Record::MData(x) => {
                self.s(r#"{"ie":"#)
                    .n(id)
                    .s(r#","mdata":{"expr":"#)
                    .n(*x)
                    .s("}}");
            }
            Record::Meta(_) | Record::Decl(_) | Record::End(_) => unreachable!(),
        }
        self.emit()
    }

    fn finish(mut self) -> Result<W> {
        self.out.flush()?;
        Ok(self.out)
    }
}

impl<W: Write> Ndjson<W> {
    fn decl(&mut self, d: &Decl) {
        match d {
            Decl::Axiom {
                head,
                is_unsafe,
                all,
            } => {
                self.s(r#"{"axiom":{"#)
                    .all_opt(all.as_ref())
                    .unsafe_(*is_unsafe)
                    .s(",")
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s("}}");
            }
            Decl::Def {
                head,
                value,
                hints,
                safety,
                all,
            } => {
                self.s(r#"{"def":{"all":"#).list(all).s(r#","hints":"#);
                match hints {
                    Hints::Opaque => self.s(r#""opaque""#),
                    Hints::Abbrev => self.s(r#""abbrev""#),
                    Hints::Regular(h) => self.s(r#"{"regular":"#).n(*h).s("}"),
                };
                let safety = match safety {
                    Safety::Safe => "safe",
                    Safety::Unsafe => "unsafe",
                    Safety::Partial => "partial",
                };
                self.s(",")
                    .lp_name(head)
                    .s(r#","safety":""#)
                    .s(safety)
                    .s(r#"","type":"#)
                    .n(head.ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Decl::Thm { head, value, all } => {
                self.s(r#"{"thm":{"all":"#)
                    .list(all)
                    .s(",")
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Decl::Opaque {
                head,
                value,
                is_unsafe,
                all,
            } => {
                self.s(r#"{"opaque":{"#)
                    .all_opt(all.as_ref())
                    .unsafe_(*is_unsafe)
                    .s(",")
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s(r#","value":"#)
                    .n(*value)
                    .s("}}");
            }
            Decl::Quot { head, kind } => {
                let kind = match kind {
                    QuotKind::Type => "type",
                    QuotKind::Ctor => "ctor",
                    QuotKind::Lift => "lift",
                    QuotKind::Ind => "ind",
                };
                self.s(r#"{"quot":{"kind":""#)
                    .s(kind)
                    .s(r#"","#)
                    .lp_name(head)
                    .s(r#","type":"#)
                    .n(head.ty)
                    .s("}}");
            }
            Decl::Inductive { types, ctors, recs } => {
                self.s(r#"{"inductive":{"ctors":["#);
                for (i, c) in ctors.iter().enumerate() {
                    self.sep(i).ctor(c);
                }
                self.s(r#"],"recs":["#);
                for (i, r) in recs.iter().enumerate() {
                    self.sep(i).rec(r);
                }
                self.s(r#"],"types":["#);
                for (i, t) in types.iter().enumerate() {
                    self.sep(i).ty(t);
                }
                self.s("]}}");
            }
        }
    }

    fn sep(&mut self, i: usize) -> &mut Self {
        if i > 0 {
            self.s(",");
        }
        self
    }
}

/// Replay lean4export NDJSON into `sink`. Ids must be consecutive, as lean4export writes them.
pub fn read<S: Sink>(input: impl BufRead, mut sink: S) -> Result<S::Output> {
    let mut next = Counts::default();
    for (n, line) in input.lines().enumerate() {
        let line = line?;
        if line.is_empty() {
            continue;
        }
        let at = |e: serde_json::Error| corrupt(format!("line {}: {e}", n + 1));
        let (id, r) = if line.starts_with(r#"{"meta":"#) {
            let m: Meta<'_> = serde_json::from_str(&line).map_err(at)?;
            (None, Record::Meta(m.meta.get().into()))
        } else {
            serde_json::from_str::<Line>(&line).map_err(at)?.record()
        };
        if let (Some(id), Some(want)) = (id, next.assign(&r)) {
            if id != want {
                return Err(corrupt(format!("line {}: id {id}, expected {want}", n + 1)));
            }
        }
        sink.record(&r)?;
    }
    sink.record(&Record::End(next))?;
    sink.finish()
}

#[derive(Deserialize)]
struct Meta<'a> {
    #[serde(borrow)]
    meta: &'a RawValue,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum Line {
    Name {
        #[serde(rename = "in")]
        id: u32,
        #[serde(flatten)]
        name: JName,
    },
    Level {
        il: u32,
        #[serde(flatten)]
        level: JLevel,
    },
    Expr {
        ie: u32,
        #[serde(flatten)]
        expr: JExpr,
    },
    Decl(JDecl),
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum JName {
    Str { pre: u32, str: String },
    Num { pre: u32, i: u64 },
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum JLevel {
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JBinding {
    binder_info: Binder,
    name: u32,
    #[serde(rename = "type")]
    ty: u32,
    body: u32,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
enum JExpr {
    Bvar(u64),
    Sort(u32),
    Const {
        name: u32,
        us: Vec<u32>,
    },
    App {
        #[serde(rename = "fn")]
        fun: u32,
        arg: u32,
    },
    Lam(JBinding),
    ForallE(JBinding),
    LetE {
        name: u32,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        body: u32,
        #[serde(default)]
        nondep: bool,
    },
    NatVal(String),
    StrVal(String),
    #[serde(rename_all = "camelCase")]
    Proj {
        type_name: u32,
        idx: u64,
        #[serde(rename = "struct")]
        struct_: u32,
    },
    Mdata {
        expr: u32,
    },
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JHead {
    name: u32,
    level_params: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
}

impl From<JHead> for Head {
    fn from(h: JHead) -> Self {
        Self {
            name: h.name,
            level_params: h.level_params,
            ty: h.ty,
        }
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum JSafety {
    Safe,
    Unsafe,
    Partial,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JUnsafe {
    #[serde(flatten)]
    head: JHead,
    #[serde(default)]
    is_unsafe: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum JDecl {
    Axiom {
        #[serde(flatten)]
        head: JUnsafe,
        all: Option<Vec<u32>>,
    },
    Def {
        #[serde(flatten)]
        head: JHead,
        value: u32,
        hints: Hints,
        safety: JSafety,
        all: Vec<u32>,
    },
    Thm {
        #[serde(flatten)]
        head: JHead,
        value: u32,
        all: Vec<u32>,
    },
    Opaque {
        #[serde(flatten)]
        head: JUnsafe,
        value: u32,
        all: Option<Vec<u32>>,
    },
    Quot {
        #[serde(flatten)]
        head: JHead,
        kind: QuotKind,
    },
    Inductive {
        types: Vec<JType>,
        ctors: Vec<JCtor>,
        recs: Vec<JRec>,
    },
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JType {
    #[serde(flatten)]
    head: JUnsafe,
    num_params: u64,
    num_indices: u64,
    all: Vec<u32>,
    ctors: Vec<u32>,
    num_nested: u64,
    is_rec: bool,
    is_reflexive: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JCtor {
    #[serde(flatten)]
    head: JUnsafe,
    induct: u32,
    cidx: u64,
    num_params: u64,
    num_fields: u64,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct JRec {
    #[serde(flatten)]
    head: JUnsafe,
    all: Vec<u32>,
    num_params: u64,
    num_indices: u64,
    num_motives: u64,
    num_minors: u64,
    rules: Vec<IndRule>,
    k: bool,
}

impl Line {
    fn record(self) -> (Option<u32>, Record<'static>) {
        match self {
            Self::Name { id, name } => (
                Some(id),
                match name {
                    JName::Str { pre, str } => Record::NameStr {
                        pre,
                        str: str.into(),
                    },
                    JName::Num { pre, i } => Record::NameNum { pre, i },
                },
            ),
            Self::Level { il, level } => (
                Some(il),
                match level {
                    JLevel::Succ(a) => Record::Succ(a),
                    JLevel::Max(a, b) => Record::Max(a, b),
                    JLevel::IMax(a, b) => Record::IMax(a, b),
                    JLevel::Param(n) => Record::Param(n),
                },
            ),
            Self::Expr { ie, expr } => (Some(ie), expr.into()),
            Self::Decl(d) => (None, Record::Decl(d.into())),
        }
    }
}

impl From<JBinding> for Binding {
    fn from(b: JBinding) -> Self {
        Self {
            info: b.binder_info,
            name: b.name,
            ty: b.ty,
            body: b.body,
        }
    }
}

impl From<JExpr> for Record<'_> {
    fn from(e: JExpr) -> Self {
        match e {
            JExpr::Bvar(i) => Self::BVar(i),
            JExpr::Sort(l) => Self::Sort(l),
            JExpr::Const { name, us } => Self::Const { name, us },
            JExpr::App { fun, arg } => Self::App { fun, arg },
            JExpr::Lam(b) => Self::Lam(b.into()),
            JExpr::ForallE(b) => Self::Pi(b.into()),
            JExpr::LetE {
                name,
                ty,
                value,
                body,
                nondep,
            } => Self::Let {
                name,
                ty,
                value,
                body,
                nondep,
            },
            JExpr::NatVal(v) => Self::Nat(v.into()),
            JExpr::StrVal(v) => Self::Str(v.into()),
            JExpr::Proj {
                type_name,
                idx,
                struct_,
            } => Self::Proj {
                type_name,
                idx,
                struct_,
            },
            JExpr::Mdata { expr } => Self::MData(expr),
        }
    }
}

impl From<JDecl> for Decl {
    fn from(d: JDecl) -> Self {
        match d {
            JDecl::Axiom { head, all } => Self::Axiom {
                head: head.head.into(),
                is_unsafe: head.is_unsafe,
                all,
            },
            JDecl::Def {
                head,
                value,
                hints,
                safety,
                all,
            } => Self::Def {
                head: head.into(),
                value,
                hints,
                safety: match safety {
                    JSafety::Safe => Safety::Safe,
                    JSafety::Unsafe => Safety::Unsafe,
                    JSafety::Partial => Safety::Partial,
                },
                all,
            },
            JDecl::Thm { head, value, all } => Self::Thm {
                head: head.into(),
                value,
                all,
            },
            JDecl::Opaque { head, value, all } => Self::Opaque {
                head: head.head.into(),
                value,
                is_unsafe: head.is_unsafe,
                all,
            },
            JDecl::Quot { head, kind } => Self::Quot {
                head: head.into(),
                kind,
            },
            JDecl::Inductive { types, ctors, recs } => Self::Inductive {
                types: types
                    .into_iter()
                    .map(|t| IndType {
                        head: t.head.head.into(),
                        is_unsafe: t.head.is_unsafe,
                        num_params: t.num_params,
                        num_indices: t.num_indices,
                        all: t.all,
                        ctors: t.ctors,
                        num_nested: t.num_nested,
                        is_rec: t.is_rec,
                        is_reflexive: t.is_reflexive,
                    })
                    .collect(),
                ctors: ctors
                    .into_iter()
                    .map(|c| IndCtor {
                        head: c.head.head.into(),
                        is_unsafe: c.head.is_unsafe,
                        induct: c.induct,
                        cidx: c.cidx,
                        num_params: c.num_params,
                        num_fields: c.num_fields,
                    })
                    .collect(),
                recs: recs
                    .into_iter()
                    .map(|r| IndRec {
                        head: r.head.head.into(),
                        is_unsafe: r.head.is_unsafe,
                        all: r.all,
                        num_params: r.num_params,
                        num_indices: r.num_indices,
                        num_motives: r.num_motives,
                        num_minors: r.num_minors,
                        rules: r.rules,
                        k: r.k,
                    })
                    .collect(),
            },
        }
    }
}
