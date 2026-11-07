use super::{
    term::{Body, Const, Ctor, Defn, Expr, ExprId, Inductive, Kind, NameId, Rec},
    Env,
};
use crate::error::{corrupt, Error, Result};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{mem, path::PathBuf};

/// Constants the kernel relies on without a term naming them: `Nat` for numeric literals,
/// what string literals unfold to, and `Eq` with the quotient constants.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Builtins {
    nat: Option<NameId>,
    strs: [Option<NameId>; 2],
    pub(crate) quot: [Option<NameId>; 5],
}

impl Builtins {
    pub(crate) fn find(env: &Env) -> Self {
        let find = |s| env.find_name(s);
        Self {
            nat: find("Nat"),
            strs: [find("Char.ofNat"), find("String.ofList")],
            quot: ["Eq", "Quot", "Quot.mk", "Quot.lift", "Quot.ind"].map(find),
        }
    }
}

/// How much of a constant a walk follows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Depth {
    /// Everything, proofs included.
    Full,
    /// Theorems as axioms over their types, as [`crate::Exporter::statements`] writes them.
    Statements,
}

/// Something a constant or term mentions.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Dep {
    Expr(ExprId),
    Const(NameId),
    /// Declared together with the constant, in one inductive or quotient block.
    Member(NameId),
    /// Reached through a literal rather than named.
    Literal(NameId),
    /// A theorem whose value is still in its olean.
    Unloaded(NameId),
}

/// An inductive block: its types, their constructors, and the recursors.
pub(crate) struct Family<'e> {
    pub(crate) types: Vec<(&'e Const, &'e Inductive)>,
    pub(crate) ctors: Vec<(&'e Const, &'e Ctor)>,
    pub(crate) recs: Vec<(&'e Const, &'e Rec)>,
}

impl<'e> Family<'e> {
    fn consts(&self) -> impl Iterator<Item = &'e Const> + '_ {
        let ctors = self.ctors.iter().map(|&(k, _)| k);
        let recs = self.recs.iter().map(|&(k, _)| k);
        self.types.iter().map(|&(k, _)| k).chain(ctors).chain(recs)
    }

    /// Every term of the block, in the order lean4export visits them.
    fn terms(&self) -> impl Iterator<Item = ExprId> + '_ {
        let rules = self
            .recs
            .iter()
            .flat_map(|(_, r)| r.rules.iter().map(|u| u.rhs));
        self.consts().map(|k| k.ty).chain(rules)
    }
}

/// What a decoding walk has visited, kept across its rounds.
pub(super) struct Walk {
    consts: FxHashSet<NameId>,
    exprs: Vec<bool>,
    depth: Depth,
}

impl Walk {
    fn new(depth: Depth) -> Self {
        Self {
            consts: FxHashSet::default(),
            exprs: Vec::new(),
            depth,
        }
    }
}

impl Env {
    /// Like [`Env::load_with`], but decode only the theorem values that exporting `consts`
    /// reaches. The rest stay in their oleans, as `None`.
    pub fn load_cone(
        search: &[PathBuf],
        roots: &[&str],
        consts: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        let mut env = Self::build(search, roots, jobs, progress, true, true)?;
        let mut live = env.live.take().expect("built live");
        let mut todo = consts
            .iter()
            .map(|c| {
                env.find_name(c)
                    .map(Dep::Const)
                    .ok_or_else(|| Error::UnknownConstant((*c).to_owned()))
            })
            .collect::<Result<Vec<_>>>()?;
        let pending: FxHashMap<NameId, (usize, u64)> = live
            .loaded
            .iter()
            .enumerate()
            .flat_map(|(i, l)| l.pending.iter().map(move |&(n, o)| (n, (i, o))))
            .collect();
        let mut walk = Walk::new(Depth::Full);
        loop {
            let mut due: Vec<_> = env
                .walk(&mut walk, todo)?
                .into_iter()
                .map(|n| (pending[&n], n))
                .collect();
            if due.is_empty() {
                env.live = Some(live);
                return Ok(env);
            }
            due.sort_unstable_by_key(|&(p, _)| p);
            todo = Vec::new();
            for (n, v) in env.decode_values(&mut live, &due)? {
                if let Some(Const {
                    kind: Kind::Thm(t), ..
                }) = env.consts.get_mut(&n)
                {
                    t.value = Some(v);
                }
                todo.push(Dep::Expr(v));
            }
        }
    }

    /// Load like [`Env::load_with`], leaving every theorem value undecoded, for
    /// [`Env::statement`] and [`crate::Exporter::statements`].
    pub fn load_statements(
        search: &[PathBuf],
        roots: &[&str],
        jobs: usize,
        progress: &(dyn Fn(usize, usize) + Sync),
    ) -> Result<Self> {
        Self::build(search, roots, jobs, progress, false, true)
    }

    /// What the statements of `consts` rest on, with the index of each one's module, in
    /// load order: everything their types mention, and through it the values of
    /// definitions and whole inductive families, but no proof. A theorem reached inside a
    /// definition is taken as stated, as [`crate::Exporter::statements`] writes it.
    pub fn statement(&self, consts: &[NameId]) -> Result<Vec<(usize, NameId)>> {
        let mut w = Walk::new(Depth::Statements);
        let todo = consts
            .iter()
            .map(|&c| {
                self.consts
                    .contains_key(&c)
                    .then_some(Dep::Const(c))
                    .ok_or_else(|| Error::UnknownConstant(self.display(c)))
            })
            .collect::<Result<_>>()?;
        self.walk(&mut w, todo)?;
        let mut module = 0;
        Ok(self
            .order
            .iter()
            .enumerate()
            .filter_map(|(i, c)| {
                while self.ends.get(module).is_some_and(|&end| i >= end) {
                    module += 1;
                }
                w.consts.contains(c).then_some((module, *c))
            })
            .collect())
    }

    /// Continue `w` from `todo` over everything an export of it would visit, returning the
    /// theorems reached whose values are not decoded.
    fn walk(&self, w: &mut Walk, mut todo: Vec<Dep>) -> Result<Vec<NameId>> {
        w.exprs.resize(self.exprs.bound(), false);
        let b = Builtins::find(self);
        let mut out = Vec::new();
        while let Some(dep) = todo.pop() {
            match dep {
                Dep::Expr(e) => {
                    if !mem::replace(&mut w.exprs[e.index()], true) {
                        self.children(e, &b, |d| todo.push(d));
                    }
                }
                Dep::Const(c) | Dep::Member(c) | Dep::Literal(c) => {
                    if !w.consts.insert(c) {
                        continue;
                    }
                    if let Some(k) = self.consts.get(&c) {
                        self.mentions(k, w.depth, &b, |d| todo.push(d))?;
                    }
                }
                Dep::Unloaded(c) => out.push(c),
            }
        }
        Ok(out)
    }

    /// The immediate subterms of `e` and the constants it names or its literals need.
    pub(crate) fn children(&self, e: ExprId, b: &Builtins, mut f: impl FnMut(Dep)) {
        match &self.exprs[e] {
            Expr::Const(n, _) => f(Dep::Const(*n)),
            Expr::App(x, y) | Expr::Lam(_, x, y, _) | Expr::Pi(_, x, y, _) => {
                f(Dep::Expr(*x));
                f(Dep::Expr(*y));
            }
            Expr::Let(_, t, v, x) => [t, v, x].into_iter().for_each(|&e| f(Dep::Expr(e))),
            Expr::Proj(_, _, x) => f(Dep::Expr(*x)),
            Expr::Nat(_) => b.nat.into_iter().for_each(|c| f(Dep::Literal(c))),
            Expr::Str(_) => b
                .strs
                .into_iter()
                .flatten()
                .for_each(|c| f(Dep::Literal(c))),
            Expr::BVar(_) | Expr::Sort(_) => {}
        }
    }

    /// What declaring `k` mentions at `depth`, in the order lean4export visits it. A
    /// constructor or recursor leads to its inductive, which declares the whole block.
    pub(crate) fn mentions(
        &self,
        k: &Const,
        depth: Depth,
        b: &Builtins,
        mut f: impl FnMut(Dep),
    ) -> Result<()> {
        let mut ty = || f(Dep::Expr(k.ty));
        match &k.kind {
            Kind::Axiom => ty(),
            Kind::Thm(_) if depth == Depth::Statements => ty(),
            Kind::Defn(Defn { value, .. }) | Kind::Opaque(Body { value, .. }) => {
                ty();
                f(Dep::Expr(*value));
            }
            Kind::Thm(t) => {
                ty();
                f(t.value.map_or(Dep::Unloaded(k.name), Dep::Expr));
            }
            Kind::Quot(_) => {
                let [eq, quot @ ..] = b.quot;
                quot.into_iter().flatten().for_each(|c| f(Dep::Member(c)));
                if let Some(eq) = eq {
                    f(Dep::Const(eq));
                }
            }
            Kind::Induct(ind) => {
                let fam = self.family(k, ind)?;
                fam.consts().for_each(|c| f(Dep::Member(c.name)));
                fam.terms().for_each(|e| f(Dep::Expr(e)));
            }
            Kind::Ctor(c) => f(Dep::Const(c.induct)),
            Kind::Rec(r) => r.all.iter().for_each(|&i| f(Dep::Const(i))),
        }
        Ok(())
    }

    /// The mutual block of `base`: its types, their constructors and their recursors.
    pub(crate) fn family<'e>(&'e self, base: &Const, ind: &'e Inductive) -> Result<Family<'e>> {
        let types = ind
            .all
            .iter()
            .map(|&n| {
                self.lookup(n, "inductive", |k| match k {
                    Kind::Induct(i) => Some(i),
                    _ => None,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let ctors = types
            .iter()
            .flat_map(|(_, i)| &i.ctors)
            .map(|&c| {
                self.lookup(c, "constructor", |k| match k {
                    Kind::Ctor(c) => Some(c),
                    _ => None,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let recs = self
            .recursors
            .get(&base.name)
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .map(|&r| {
                self.lookup(r, "recursor", |k| match k {
                    Kind::Rec(r) => Some(r),
                    _ => None,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Family { types, ctors, recs })
    }

    /// The constant `n` as the kind `pick` selects, `what` naming it in the error.
    pub(crate) fn lookup<'e, T>(
        &'e self,
        n: NameId,
        what: &str,
        pick: impl Fn(&'e Kind) -> Option<&'e T>,
    ) -> Result<(&'e Const, &'e T)> {
        self.consts
            .get(&n)
            .and_then(|c| Some((c, pick(&c.kind)?)))
            .ok_or_else(|| corrupt(format!("{} is not a known {what}", self.display(n))))
    }
}
