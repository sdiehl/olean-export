use crate::env::{
    Binder, Const, Env, Expr, ExprId, Hints, Kind, Level, LevelId, Name, NameId, QuotKind, ANON,
    ZERO,
};
use rustc_hash::FxHashSet;
use std::{
    fmt::Write as _,
    io::{self, Write},
};

const UNSEEN: u32 = u32::MAX;

/// Streams an [`Env`] in the lean4export 3.1.0 NDJSON format. Ids are assigned on first
/// use and every line only refers to lines already written.
#[derive(Debug)]
pub struct Exporter<'a, W: Write> {
    env: &'a Env,
    out: W,
    names: Vec<u32>,
    levels: Vec<u32>,
    exprs: Vec<u32>,
    next: [u32; 3],
    scanned: Vec<bool>,
    visited: FxHashSet<NameId>,
    nat: Option<NameId>,
    str_deps: [Option<NameId>; 2],
    quot: [Option<NameId>; 5],
}

impl<'a, W: Write> Exporter<'a, W> {
    pub fn new(env: &'a Env, out: W) -> Self {
        let mut names = vec![UNSEEN; env.names.len()];
        let mut levels = vec![UNSEEN; env.levels.len()];
        names[ANON as usize] = 0;
        levels[ZERO as usize] = 0;
        let find = |s| env.find_name(s);
        Self {
            env,
            out,
            names,
            levels,
            exprs: vec![UNSEEN; env.exprs.len()],
            next: [1, 1, 0],
            scanned: vec![false; env.exprs.len()],
            visited: FxHashSet::default(),
            nat: find("Nat"),
            str_deps: [find("Char.ofNat"), find("String.ofList")],
            quot: [
                find("Eq"),
                find("Quot"),
                find("Quot.mk"),
                find("Quot.lift"),
                find("Quot.ind"),
            ],
        }
    }

    pub fn meta(&mut self) -> io::Result<()> {
        let h = &self.env.header;
        writeln!(
            self.out,
            r#"{{"meta":{{"exporter":{{"name":"tiny-olean","version":"{}"}},"format":{{"version":"3.1.0"}},"lean":{{"githash":"{}","version":"{}"}}}}}}"#,
            env!("CARGO_PKG_VERSION"),
            h.githash,
            h.version
        )
    }

    /// Export every non-internal constant in load order, like `lean4export` with no `--`.
    pub fn all(&mut self) -> io::Result<()> {
        self.env.roots().try_for_each(|c| self.constant(c))
    }

    /// Lines written so far for names, levels and expressions.
    #[must_use]
    pub const fn counts(&self) -> [u32; 3] {
        self.next
    }

    pub fn finish(mut self) -> io::Result<W> {
        self.out.flush()?;
        Ok(self.out)
    }

    fn line(&mut self, s: &str) -> io::Result<()> {
        self.out.write_all(s.as_bytes())?;
        self.out.write_all(b"\n")
    }

    const fn fresh(&mut self, table: usize) -> u32 {
        let id = self.next[table];
        self.next[table] += 1;
        id
    }

    fn name(&mut self, n: NameId) -> io::Result<u32> {
        if self.names[n as usize] != UNSEEN {
            return Ok(self.names[n as usize]);
        }
        let s = match &self.env.names[n] {
            Name::Anon => unreachable!(),
            Name::Str(p, s) => {
                let p = self.name(*p)?;
                let id = self.fresh(0);
                format!(r#"{{"in":{id},"str":{{"pre":{p},"str":{}}}}}"#, quote(s))
            }
            Name::Num(p, i) => {
                let p = self.name(*p)?;
                let id = self.fresh(0);
                format!(r#"{{"in":{id},"num":{{"i":{i},"pre":{p}}}}}"#)
            }
        };
        self.line(&s)?;
        self.names[n as usize] = self.next[0] - 1;
        Ok(self.next[0] - 1)
    }

    fn name_list(&mut self, ns: &[NameId]) -> io::Result<String> {
        let ids = ns
            .iter()
            .map(|&n| self.name(n))
            .collect::<io::Result<Vec<_>>>()?;
        Ok(json_list(&ids))
    }

    fn level_params(&mut self, ps: &[NameId]) -> io::Result<String> {
        let list = self.name_list(ps)?;
        for &p in ps {
            let l = self
                .env
                .levels
                .get(&Level::Param(p))
                .expect("level params are interned at load");
            self.level(l)?;
        }
        Ok(list)
    }

    fn level(&mut self, l: LevelId) -> io::Result<u32> {
        if self.levels[l as usize] != UNSEEN {
            return Ok(self.levels[l as usize]);
        }
        let body = match self.env.levels[l] {
            Level::Zero => unreachable!(),
            Level::Succ(a) => format!(r#""succ":{}"#, self.level(a)?),
            Level::Max(a, b) => format!(r#""max":[{},{}]"#, self.level(a)?, self.level(b)?),
            Level::IMax(a, b) => format!(r#""imax":[{},{}]"#, self.level(a)?, self.level(b)?),
            Level::Param(n) => format!(r#""param":{}"#, self.name(n)?),
        };
        let id = self.fresh(1);
        self.line(&format!(r#"{{"il":{id},{body}}}"#))?;
        self.levels[l as usize] = id;
        Ok(id)
    }

    fn expr(&mut self, e: ExprId) -> io::Result<u32> {
        if self.exprs[e as usize] != UNSEEN {
            return Ok(self.exprs[e as usize]);
        }
        let s = match &self.env.exprs[e] {
            Expr::BVar(i) => format!(r#"{{"bvar":{i},"ie":{}}}"#, self.fresh(2)),
            Expr::Sort(l) => {
                let l = self.level(*l)?;
                format!(r#"{{"ie":{},"sort":{l}}}"#, self.fresh(2))
            }
            Expr::Const(n, us) => {
                let n = self.name(*n)?;
                let us = us
                    .iter()
                    .map(|&u| self.level(u))
                    .collect::<io::Result<Vec<_>>>()?;
                format!(
                    r#"{{"const":{{"name":{n},"us":{}}},"ie":{}}}"#,
                    json_list(&us),
                    self.fresh(2)
                )
            }
            Expr::App(f, a) => {
                let (f, a) = (self.expr(*f)?, self.expr(*a)?);
                format!(r#"{{"app":{{"arg":{a},"fn":{f}}},"ie":{}}}"#, self.fresh(2))
            }
            Expr::Lam(n, t, b, bi) | Expr::Pi(n, t, b, bi) => {
                let (n, t, b) = (self.name(*n)?, self.expr(*t)?, self.expr(*b)?);
                let body = format!(
                    r#"{{"binderInfo":"{}","body":{b},"name":{n},"type":{t}}}"#,
                    binder(*bi)
                );
                let id = self.fresh(2);
                if matches!(self.env.exprs[e], Expr::Lam(..)) {
                    format!(r#"{{"ie":{id},"lam":{body}}}"#)
                } else {
                    format!(r#"{{"forallE":{body},"ie":{id}}}"#)
                }
            }
            Expr::Let(n, t, v, b) => {
                let (n, t, v, b) = (
                    self.name(*n)?,
                    self.expr(*t)?,
                    self.expr(*v)?,
                    self.expr(*b)?,
                );
                let id = self.fresh(2);
                format!(
                    r#"{{"ie":{id},"letE":{{"body":{b},"name":{n},"nondep":false,"type":{t},"value":{v}}}}}"#
                )
            }
            Expr::Nat(v) => {
                if let Some(nat) = self.nat {
                    self.constant(nat)?;
                }
                format!(r#"{{"ie":{},"natVal":"{v}"}}"#, self.fresh(2))
            }
            Expr::Str(v) => {
                for c in self.str_deps.into_iter().flatten() {
                    self.constant(c)?;
                }
                format!(r#"{{"ie":{},"strVal":{}}}"#, self.fresh(2), quote(v))
            }
            Expr::Proj(n, i, x) => {
                let (n, x) = (self.name(*n)?, self.expr(*x)?);
                format!(
                    r#"{{"ie":{},"proj":{{"idx":{i},"struct":{x},"typeName":{n}}}}}"#,
                    self.fresh(2)
                )
            }
        };
        self.line(&s)?;
        self.exprs[e as usize] = self.next[2] - 1;
        Ok(self.next[2] - 1)
    }

    fn deps(&mut self, e: ExprId) -> io::Result<()> {
        if self.scanned[e as usize] {
            return Ok(());
        }
        match &self.env.exprs[e] {
            Expr::Const(n, _) => self.constant(*n)?,
            Expr::App(a, b) | Expr::Lam(_, a, b, _) | Expr::Pi(_, a, b, _) => {
                self.deps(*a)?;
                self.deps(*b)?;
            }
            Expr::Let(_, t, v, b) => {
                self.deps(*t)?;
                self.deps(*v)?;
                self.deps(*b)?;
            }
            Expr::Proj(_, _, x) => self.deps(*x)?,
            Expr::BVar(_) | Expr::Sort(_) | Expr::Nat(_) | Expr::Str(_) => {}
        }
        self.scanned[e as usize] = true;
        Ok(())
    }

    /// Export a constant and, first, everything it mentions.
    pub fn constant(&mut self, c: NameId) -> io::Result<()> {
        if !self.visited.insert(c) {
            return Ok(());
        }
        let env = self.env;
        let Some(k) = env.consts.get(&c) else {
            return Ok(());
        };
        match &k.kind {
            Kind::Axiom => {
                self.deps(k.ty)?;
                let (n, lp, t) = self.header(k)?;
                self.line(&format!(
                    r#"{{"axiom":{{"isUnsafe":false,"levelParams":{lp},"name":{n},"type":{t}}}}}"#
                ))
            }
            Kind::Defn { value, hints, all } => {
                self.deps(k.ty)?;
                self.deps(*value)?;
                let (n, lp, t) = self.header(k)?;
                let v = self.expr(*value)?;
                let all = self.name_list(all)?;
                let hints = match hints {
                    Hints::Opaque => r#""opaque""#.to_owned(),
                    Hints::Abbrev => r#""abbrev""#.to_owned(),
                    Hints::Regular(h) => format!(r#"{{"regular":{h}}}"#),
                };
                self.line(&format!(
                    r#"{{"def":{{"all":{all},"hints":{hints},"levelParams":{lp},"name":{n},"safety":"safe","type":{t},"value":{v}}}}}"#
                ))
            }
            Kind::Thm { value, all } | Kind::Opaque { value, all } => {
                self.deps(k.ty)?;
                self.deps(*value)?;
                let (n, lp, t) = self.header(k)?;
                let v = self.expr(*value)?;
                let all = self.name_list(all)?;
                if matches!(k.kind, Kind::Thm { .. }) {
                    self.line(&format!(r#"{{"thm":{{"all":{all},"levelParams":{lp},"name":{n},"type":{t},"value":{v}}}}}"#))
                } else {
                    self.line(&format!(
                        r#"{{"opaque":{{"all":{all},"isUnsafe":false,"levelParams":{lp},"name":{n},"type":{t},"value":{v}}}}}"#
                    ))
                }
            }
            Kind::Quot(_) => self.quot(),
            Kind::Induct { .. } => self.inductive(k),
            Kind::Ctor { induct, .. } => self.constant(*induct),
            Kind::Rec { all, .. } => all.iter().try_for_each(|&i| self.constant(i)),
        }
    }

    fn header(&mut self, k: &Const) -> io::Result<(u32, String, u32)> {
        Ok((
            self.name(k.name)?,
            self.level_params(&k.level_params)?,
            self.expr(k.ty)?,
        ))
    }

    fn quot(&mut self) -> io::Result<()> {
        let [eq, rest @ ..] = self.quot;
        if let Some(eq) = eq {
            self.constant(eq)?;
        }
        for c in rest.into_iter().flatten() {
            self.visited.insert(c);
            let k = &self.env.consts[&c];
            let Kind::Quot(kind) = k.kind else {
                unreachable!()
            };
            let (n, lp, t) = self.header(k)?;
            let kind = match kind {
                QuotKind::Type => "type",
                QuotKind::Ctor => "ctor",
                QuotKind::Lift => "lift",
                QuotKind::Ind => "ind",
            };
            self.line(&format!(
                r#"{{"quot":{{"kind":"{kind}","levelParams":{lp},"name":{n},"type":{t}}}}}"#
            ))?;
        }
        Ok(())
    }

    fn inductive(&mut self, base: &Const) -> io::Result<()> {
        let env = self.env;
        let Kind::Induct { all, .. } = &base.kind else {
            unreachable!()
        };
        let types: Vec<&Const> = all.iter().map(|n| &env.consts[n]).collect();
        let mut ctors = Vec::new();
        for t in &types {
            let Kind::Induct { ctors: cs, .. } = &t.kind else {
                unreachable!()
            };
            ctors.extend(cs.iter().map(|c| &env.consts[c]));
            self.visited.insert(t.name);
            self.deps(t.ty)?;
        }
        for c in &ctors {
            self.visited.insert(c.name);
            self.deps(c.ty)?;
        }
        let recs: Vec<&Const> = env
            .recursors
            .get(&base.name)
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .map(|r| &env.consts[r])
            .collect();
        for r in &recs {
            self.visited.insert(r.name);
            self.deps(r.ty)?;
        }
        for r in &recs {
            let Kind::Rec { rules, .. } = &r.kind else {
                unreachable!()
            };
            for rule in rules {
                self.deps(rule.rhs)?;
            }
        }
        let mut out = String::from(r#"{"inductive":{"ctors":["#);
        for (i, c) in ctors.iter().enumerate() {
            let Kind::Ctor {
                induct,
                cidx,
                num_params,
                num_fields,
            } = c.kind
            else {
                unreachable!()
            };
            let (n, lp, t) = self.header(c)?;
            let induct = self.name(induct)?;
            sep(&mut out, i);
            let _ = write!(
                out,
                r#"{{"cidx":{cidx},"induct":{induct},"isUnsafe":false,"levelParams":{lp},"name":{n},"numFields":{num_fields},"numParams":{num_params},"type":{t}}}"#
            );
        }
        out.push_str(r#"],"recs":["#);
        for (i, r) in recs.iter().enumerate() {
            let Kind::Rec {
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
            } = &r.kind
            else {
                unreachable!()
            };
            let (n, lp, t) = self.header(r)?;
            let all = self.name_list(all)?;
            let mut rs = String::new();
            for (j, rule) in rules.iter().enumerate() {
                let (ctor, rhs) = (self.name(rule.ctor)?, self.expr(rule.rhs)?);
                sep(&mut rs, j);
                let _ = write!(
                    rs,
                    r#"{{"ctor":{ctor},"nfields":{},"rhs":{rhs}}}"#,
                    rule.nfields
                );
            }
            sep(&mut out, i);
            let _ = write!(
                out,
                r#"{{"all":{all},"isUnsafe":false,"k":{k},"levelParams":{lp},"name":{n},"numIndices":{num_indices},"numMinors":{num_minors},"numMotives":{num_motives},"numParams":{num_params},"rules":[{rs}],"type":{t}}}"#
            );
        }
        out.push_str(r#"],"types":["#);
        for (i, ty) in types.iter().enumerate() {
            let Kind::Induct {
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_reflexive,
            } = &ty.kind
            else {
                unreachable!()
            };
            let (n, lp, t) = self.header(ty)?;
            let (all, ctors) = (self.name_list(all)?, self.name_list(ctors)?);
            sep(&mut out, i);
            let _ = write!(
                out,
                r#"{{"all":{all},"ctors":{ctors},"isRec":{is_rec},"isReflexive":{is_reflexive},"isUnsafe":false,"levelParams":{lp},"name":{n},"numIndices":{num_indices},"numNested":{num_nested},"numParams":{num_params},"type":{t}}}"#
            );
        }
        out.push_str("]}}");
        self.line(&out)
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

fn sep(s: &mut String, i: usize) {
    if i > 0 {
        s.push(',');
    }
}

fn json_list(ids: &[u32]) -> String {
    let mut s = String::from("[");
    for (i, id) in ids.iter().enumerate() {
        sep(&mut s, i);
        let _ = write!(s, "{id}");
    }
    s.push(']');
    s
}

fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || c == '\u{7f}' => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
