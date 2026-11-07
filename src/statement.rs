//! What a theorem's statement rests on, printed as raw terms for a person to review.
//!
//! Notation, coercions and macros never reach an olean, so the terms print exactly as the
//! kernel sees them, in Lean syntax but without notation, and nothing can hide behind it.

use crate::{
    env::{resolve, Binder, Env, Expr, ExprId, Hints, Kind, Level, LevelId, NameId},
    error::Result,
    olean::{small_nat, Image},
};
use rustc_hash::FxHashMap;
use std::{fmt::Write as _, io::Write, path::PathBuf};

/// Print the statements of `roots` and what they rest on, outside the modules `trust` names.
///
/// Every definition, inductive, opaque and axiom reached prints in load order with the lines
/// of source it came from. A module is trusted if a name in `trust` is it or a prefix of it.
/// Each term stops after `max` characters, if not 0.
pub fn report(
    env: &Env,
    search: &[PathBuf],
    roots: &[NameId],
    trust: &[String],
    max: usize,
    out: &mut dyn Write,
) -> Result<()> {
    let cone = env.statement(roots);
    let trusted = |m: usize| {
        let m = &env.modules[m];
        trust.iter().any(|t| {
            m == t
                || m.strip_prefix(t.as_str())
                    .is_some_and(|r| r.starts_with('.'))
        })
    };
    // constructors and recursors print with their inductive, and theorems by name only
    let listed = |&(_, c): &(usize, NameId)| {
        !roots.contains(&c)
            && !matches!(
                env.consts[&c].kind,
                Kind::Thm(_) | Kind::Ctor(_) | Kind::Rec(_)
            )
    };
    let (hidden, shown): (Vec<_>, Vec<_>) = cone
        .iter()
        .copied()
        .filter(listed)
        .partition(|&(m, _)| trusted(m));
    let mut axioms: Vec<String> = cone
        .iter()
        .filter(|(_, c)| matches!(env.consts[c].kind, Kind::Axiom))
        .map(|&(_, c)| env.display(c))
        .collect();
    if axioms.is_empty() {
        axioms.push("none".into());
    }
    let mut modules: Vec<usize> = shown.iter().map(|&(m, _)| m).collect();
    modules.dedup();
    let names: Vec<String> = roots.iter().map(|&c| env.display(c)).collect();
    let plural = |n: usize, what: &str| format!("{n} {what}{}", if n == 1 { "" } else { "s" });
    write!(
        out,
        "-- {} rests on {} in {}",
        names.join(", "),
        plural(shown.len(), "declaration"),
        plural(modules.len(), "module"),
    )?;
    if !trust.is_empty() {
        write!(out, ", and {} more in {}", hidden.len(), trust.join(", "))?;
    }
    writeln!(out, "\n-- axioms: {}", axioms.join(", "))?;
    let mut p = Printer::new(env, max);
    let mut lines = FxHashMap::default();
    let module_of = |c| cone.iter().find(|&&(_, d)| d == c).map_or(0, |&(m, _)| m);
    let roots = roots.iter().map(|&c| (module_of(c), c));
    for (m, c) in roots.chain(shown) {
        let module = &env.modules[m];
        if let std::collections::hash_map::Entry::Vacant(e) = lines.entry(m) {
            e.insert(ranges(&resolve(search, module)?)?);
        }
        let file = format!("{}.lean", module.replace('.', "/"));
        let at = match lines[&m].get(&env.display(c)) {
            Some((a, b)) if a == b => format!("{file}:{a}"),
            Some((a, b)) => format!("{file}:{a}-{b}"),
            None => file,
        };
        writeln!(out, "\n-- {at}\n{}", p.decl(c))?;
    }
    Ok(())
}

/// The first and last source line of each declaration of a module, from `declRangeExt`.
fn ranges(path: &std::path::Path) -> Result<FxHashMap<String, (u64, u64)>> {
    let img = Image::open_module(path)?;
    let mut out = FxHashMap::default();
    for e in img.array(img.field(img.root, 4)?)? {
        if img.str_name(img.field(e, 0)?)? != "Lean.declRangeExt" {
            continue;
        }
        for d in img.array(img.field(e, 1)?)? {
            let range = img.field(img.field(d, 1)?, 0)?;
            let line = |pos| img.field(pos, 0).and_then(small_nat);
            let span = (line(img.field(range, 0)?)?, line(img.field(range, 2)?)?);
            out.insert(img.str_name(img.field(d, 0)?)?, span);
        }
    }
    Ok(out)
}

/// Prints declarations and terms without notation, naming bound variables apart.
struct Printer<'e> {
    env: &'e Env,
    max: usize,
    out: String,
    scope: Vec<String>,
    loose: FxHashMap<ExprId, u64>,
}

/// Contexts, loosest first: a binder body, an arrow's domain, an application's argument.
const TOP: u8 = 0;
const DOMAIN: u8 = 1;
const ARG: u8 = 2;

impl<'e> Printer<'e> {
    fn new(env: &'e Env, max: usize) -> Self {
        Self {
            env,
            max,
            out: String::new(),
            scope: Vec::new(),
            loose: FxHashMap::default(),
        }
    }

    fn decl(&mut self, c: NameId) -> String {
        let env = self.env;
        let k = &env.consts[&c];
        let (word, value) = match &k.kind {
            Kind::Axiom => ("axiom", None),
            Kind::Defn(d) if d.hints == Hints::Abbrev => ("abbrev", Some(d.value)),
            Kind::Defn(d) => ("def", Some(d.value)),
            Kind::Thm(_) => ("theorem", None),
            Kind::Opaque(_) => ("opaque", None),
            Kind::Quot(_) => ("quot", None),
            Kind::Induct(_) => ("inductive", None),
            Kind::Ctor(_) => ("ctor", None),
            Kind::Rec(_) => ("recursor", None),
        };
        let mut s = format!("{word} {}", self.head(c));
        if let Some(v) = value {
            write!(s, " :=\n  {}", self.term(v)).expect("string");
        }
        if let Kind::Induct(i) = &k.kind {
            for &ctor in &i.ctors {
                write!(s, "\n| {}", self.head(ctor)).expect("string");
            }
        }
        s
    }

    fn head(&mut self, c: NameId) -> String {
        let k = &self.env.consts[&c];
        let ps: Vec<String> = k
            .level_params
            .iter()
            .map(|&n| self.env.display(n))
            .collect();
        let us = if ps.is_empty() {
            String::new()
        } else {
            format!(".{{{}}}", ps.join(", "))
        };
        format!("{}{us} : {}", self.env.display(c), self.term(k.ty))
    }

    fn term(&mut self, e: ExprId) -> String {
        self.out.clear();
        self.expr(e, TOP);
        let mut s = std::mem::take(&mut self.out);
        if self.max > 0 && s.len() > self.max {
            let mut cut = self.max;
            while !s.is_char_boundary(cut) {
                cut -= 1;
            }
            s.truncate(cut);
            s.push_str(" ...[cut]");
        }
        s
    }

    const fn full(&self) -> bool {
        self.max > 0 && self.out.len() > self.max
    }

    fn open(&mut self, on: bool) {
        if on {
            self.out.push('(');
        }
    }

    fn close(&mut self, on: bool) {
        if on {
            self.out.push(')');
        }
    }

    fn expr(&mut self, e: ExprId, prec: u8) {
        if self.full() {
            return;
        }
        let env = self.env;
        match &env.exprs[e] {
            Expr::BVar(i) => {
                let name = usize::try_from(*i)
                    .ok()
                    .and_then(|i| self.scope.len().checked_sub(i + 1))
                    .map_or_else(|| format!("#{i}"), |j| self.scope[j].clone());
                self.out.push_str(&name);
            }
            Expr::Sort(l) => {
                let s = sort(env, *l);
                let paren = prec >= ARG && s.contains(' ');
                self.open(paren);
                self.out.push_str(&s);
                self.close(paren);
            }
            Expr::Const(n, us) => {
                self.out.push_str(&env.display(*n));
                if !us.is_empty() {
                    let us: Vec<String> = us.iter().map(|&u| level(env, u, false)).collect();
                    write!(self.out, ".{{{}}}", us.join(", ")).expect("string");
                }
            }
            Expr::App(..) => {
                let mut args = Vec::new();
                let mut f = e;
                while let Expr::App(g, a) = &env.exprs[f] {
                    args.push(*a);
                    f = *g;
                }
                self.open(prec >= ARG);
                self.expr(f, ARG);
                for &a in args.iter().rev() {
                    self.out.push(' ');
                    self.expr(a, ARG);
                }
                self.close(prec >= ARG);
            }
            Expr::Lam(..) => {
                self.open(prec > TOP);
                self.out.push_str("fun");
                let depth = self.scope.len();
                let body = self.binders(e, true);
                self.out.push_str(" => ");
                self.expr(body, TOP);
                self.scope.truncate(depth);
                self.close(prec > TOP);
            }
            Expr::Pi(_, ty, body, bi) if *bi == Binder::Default && self.range(*body) == 0 => {
                self.open(prec > TOP);
                self.expr(*ty, DOMAIN);
                self.out.push_str(" → ");
                self.scope.push(String::new());
                self.expr(*body, TOP);
                self.scope.pop();
                self.close(prec > TOP);
            }
            Expr::Pi(..) => {
                self.open(prec > TOP);
                self.out.push('∀');
                let depth = self.scope.len();
                let body = self.binders(e, false);
                self.out.push_str(", ");
                self.expr(body, TOP);
                self.scope.truncate(depth);
                self.close(prec > TOP);
            }
            Expr::Let(n, ty, v, body) => {
                self.open(prec > TOP);
                let x = self.fresh(*n);
                write!(self.out, "let {x} : ").expect("string");
                self.expr(*ty, TOP);
                self.out.push_str(" := ");
                self.expr(*v, TOP);
                self.out.push_str("; ");
                self.scope.push(x);
                self.expr(*body, TOP);
                self.scope.pop();
                self.close(prec > TOP);
            }
            Expr::Nat(n) => self.out.push_str(n),
            Expr::Str(s) => write!(self.out, "{s:?}").expect("string"),
            Expr::Proj(_, i, x) => {
                self.expr(*x, ARG);
                write!(self.out, ".{}", i + 1).expect("string");
            }
        }
    }

    /// Print the run of lambdas, or of dependent or non-default pis, at `e`, pushing their
    /// names for the caller to pop, and return the body.
    fn binders(&mut self, mut e: ExprId, lam: bool) -> ExprId {
        let env = self.env;
        loop {
            let (n, ty, body, bi) = match &env.exprs[e] {
                Expr::Lam(n, t, b, bi) if lam => (*n, *t, *b, *bi),
                Expr::Pi(n, t, b, bi) if !lam && (*bi != Binder::Default || self.range(*b) > 0) => {
                    (*n, *t, *b, *bi)
                }
                _ => break,
            };
            let x = self.fresh(n);
            let (l, r) = match bi {
                Binder::Default => ("(", ")"),
                Binder::Implicit => ("{", "}"),
                Binder::StrictImplicit => ("⦃", "⦄"),
                Binder::InstImplicit => ("[", "]"),
            };
            write!(self.out, " {l}{x} : ").expect("string");
            self.expr(ty, TOP);
            self.out.push_str(r);
            self.scope.push(x);
            e = body;
        }
        e
    }

    /// One more than the largest loose bound variable of `e`, or 0 if it is closed.
    fn range(&mut self, e: ExprId) -> u64 {
        if let Some(&r) = self.loose.get(&e) {
            return r;
        }
        let r = match &self.env.exprs[e] {
            Expr::BVar(i) => i + 1,
            Expr::App(a, b) => self.range(*a).max(self.range(*b)),
            Expr::Lam(_, t, b, _) | Expr::Pi(_, t, b, _) => {
                self.range(*t).max(self.range(*b).saturating_sub(1))
            }
            Expr::Let(_, t, v, b) => self
                .range(*t)
                .max(self.range(*v))
                .max(self.range(*b).saturating_sub(1)),
            Expr::Proj(_, _, x) => self.range(*x),
            Expr::Sort(_) | Expr::Const(..) | Expr::Nat(_) | Expr::Str(_) => 0,
        };
        self.loose.insert(e, r);
        r
    }

    /// The binder's name without hygiene, made distinct from every name in scope.
    fn fresh(&self, n: NameId) -> String {
        let full = self.env.display(n);
        let base = full.split("._@").next().unwrap_or_default();
        let base = if base.is_empty() { "x" } else { base };
        let mut x = base.to_owned();
        let mut i = 1;
        while self.scope.contains(&x) {
            x = format!("{base}_{i}");
            i += 1;
        }
        x
    }
}

fn sort(env: &Env, l: LevelId) -> String {
    match &env.levels[l] {
        Level::Zero => "Prop".into(),
        Level::Succ(u) if matches!(env.levels[*u], Level::Zero) => "Type".into(),
        Level::Succ(u) => format!("Type {}", level(env, *u, true)),
        _ => format!("Sort {}", level(env, l, true)),
    }
}

fn level(env: &Env, l: LevelId, arg: bool) -> String {
    let mut n = 0;
    let mut base = l;
    while let Level::Succ(u) = &env.levels[base] {
        n += 1;
        base = *u;
    }
    let paren = |s: String| if arg { format!("({s})") } else { s };
    let b = match &env.levels[base] {
        Level::Zero => return n.to_string(),
        Level::Param(p) => env.display(*p),
        Level::Max(a, b) => paren(format!(
            "max {} {}",
            level(env, *a, true),
            level(env, *b, true)
        )),
        Level::IMax(a, b) => paren(format!(
            "imax {} {}",
            level(env, *a, true),
            level(env, *b, true)
        )),
        Level::Succ(_) => unreachable!("peeled"),
    };
    if n == 0 {
        b
    } else {
        paren(format!("{b} + {n}"))
    }
}
