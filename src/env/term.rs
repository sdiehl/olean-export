use serde::{Deserialize, Serialize};
use std::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

/// The id of a `T` in its table.
#[derive(PartialEq, Eq, Hash)]
pub struct Id<T>(pub(super) u32, PhantomData<fn() -> T>);

impl<T> Id<T> {
    pub(super) const fn new(i: u32) -> Self {
        Self(i, PhantomData)
    }

    /// The id as an index, for arrays sized by a table's `bound`.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Id<T> {}

impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

pub type NameId = Id<Name>;

pub type LevelId = Id<Level>;

pub type ExprId = Id<Expr>;

pub const ANON: NameId = Id::new(0);

pub const ZERO: LevelId = Id::new(0);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Name {
    Anon,
    Str(NameId, Box<str>),
    Num(NameId, u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Binder {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// Equality and hashing ignore binder names and annotations, matching Lean's `BEq Expr`,
/// so terms that differ only there share one id, as they do in lean4export.
#[derive(Debug, Clone)]
pub enum Expr {
    BVar(u64),
    Sort(LevelId),
    Const(NameId, Box<[LevelId]>),
    App(ExprId, ExprId),
    Lam(NameId, ExprId, ExprId, Binder),
    Pi(NameId, ExprId, ExprId, Binder),
    Let(NameId, ExprId, ExprId, ExprId),
    Nat(Box<str>),
    Str(Box<str>),
    Proj(NameId, u64, ExprId),
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::BVar(a), Self::BVar(b)) => a == b,
            (Self::Sort(a), Self::Sort(b)) => a == b,
            (Self::Const(n, us), Self::Const(m, vs)) => n == m && us == vs,
            (Self::App(f, a), Self::App(g, b)) => f == g && a == b,
            (Self::Lam(_, t, b, _), Self::Lam(_, u, c, _))
            | (Self::Pi(_, t, b, _), Self::Pi(_, u, c, _)) => t == u && b == c,
            (Self::Let(_, t, v, b), Self::Let(_, u, w, c)) => t == u && v == w && b == c,
            (Self::Nat(a), Self::Nat(b)) | (Self::Str(a), Self::Str(b)) => a == b,
            (Self::Proj(n, i, x), Self::Proj(m, j, y)) => n == m && i == j && x == y,
            _ => false,
        }
    }
}

impl Eq for Expr {}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, h: &mut H) {
        let pack = |a: u32, b: u32| u64::from(a) << 32 | u64::from(b);
        match self {
            Self::BVar(i) => h.write_u64(*i),
            Self::Sort(l) => h.write_u32(l.0),
            Self::Const(n, us) => {
                h.write_u32(n.0);
                us.iter().for_each(|u| h.write_u32(u.0));
            }
            Self::App(f, a) => h.write_u64(pack(f.0, a.0)),
            Self::Lam(_, t, b, _) | Self::Pi(_, t, b, _) => h.write_u64(pack(t.0, b.0)),
            Self::Let(_, t, v, b) => {
                h.write_u64(pack(t.0, v.0));
                h.write_u32(b.0);
            }
            Self::Nat(v) | Self::Str(v) => h.write(v.as_bytes()),
            Self::Proj(n, i, x) => {
                h.write_u64(pack(n.0, x.0));
                h.write_u64(*i);
            }
        }
        h.write_u8(self.tag());
    }
}

impl Expr {
    const fn tag(&self) -> u8 {
        match self {
            Self::BVar(_) => 0,
            Self::Sort(_) => 1,
            Self::Const(..) => 2,
            Self::App(..) => 3,
            Self::Lam(..) => 4,
            Self::Pi(..) => 5,
            Self::Let(..) => 6,
            Self::Nat(_) => 7,
            Self::Str(_) => 8,
            Self::Proj(..) => 9,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Hints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Debug)]
pub struct Rule {
    pub ctor: NameId,
    pub nfields: u64,
    pub rhs: ExprId,
}

#[derive(Debug)]
pub struct Defn {
    pub value: ExprId,
    pub hints: Hints,
    pub all: Vec<NameId>,
}

/// The value of an opaque constant.
#[derive(Debug)]
pub struct Body {
    pub value: ExprId,
    pub all: Vec<NameId>,
}

/// A theorem. Its value is `None` when [`Env::load_cone`] did not need it.
#[derive(Debug)]
pub struct Theorem {
    pub value: Option<ExprId>,
    pub all: Vec<NameId>,
}

#[derive(Debug)]
pub struct Inductive {
    pub num_params: u64,
    pub num_indices: u64,
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: u64,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

#[derive(Debug)]
pub struct Ctor {
    pub induct: NameId,
    pub cidx: u64,
    pub num_params: u64,
    pub num_fields: u64,
}

#[derive(Debug)]
pub struct Rec {
    pub all: Vec<NameId>,
    pub num_params: u64,
    pub num_indices: u64,
    pub num_motives: u64,
    pub num_minors: u64,
    pub rules: Vec<Rule>,
    pub k: bool,
}

#[derive(Debug)]
pub enum Kind {
    Axiom,
    Defn(Defn),
    Thm(Theorem),
    Opaque(Body),
    Quot(QuotKind),
    Induct(Inductive),
    Ctor(Ctor),
    Rec(Rec),
}

/// A declaration the kernel would accept. Unsafe and partial ones are dropped at load time.
#[derive(Debug)]
pub struct Const {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
    pub kind: Kind,
}
