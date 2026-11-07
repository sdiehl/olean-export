//! What a theorem's statement rests on, printed as raw terms for a person to review.
//!
//! Notation, coercions and macros never reach an olean, so the terms print as the kernel
//! sees them, in Lean syntax but without notation. A name Lean would not read back as itself
//! goes in `«»`. Binder names are only labels, from one of the copies of a shared term, so
//! they are renamed apart from each other and from the first component of every constant,
//! and no name reads as something it is not.

use crate::{
    env::{
        escape, resolve, Binder, Env, Expr, ExprId, Hints, Kind, Level, LevelId, Name, NameId, ANON,
    },
    error::Result,
    olean::{small_nat, Image},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    borrow::Cow,
    collections::hash_map::Entry,
    fmt::Write as _,
    io::Write,
    mem,
    path::{Path, PathBuf},
};

/// Print the statements of `roots` and what they rest on, outside the modules `trust` names.
///
/// Every definition, inductive, opaque, axiom and theorem reached prints in load order with
/// the lines of source it came from, theorems without their proofs. A module is trusted if a
/// name in `trust` is it or a prefix of it. Every axiom is named in the header, trusted or
/// not, but trusted theorems are only counted. Each term stops after `max` characters, if
/// not 0.
pub fn report(
    env: &Env,
    search: &[PathBuf],
    roots: &[NameId],
    trust: &[String],
    max: usize,
    out: &mut dyn Write,
) -> Result<()> {
    let cone = env.statement(roots)?;
    let trusted = |m: usize| {
        let m = &env.modules[m];
        trust.iter().any(|t| {
            m == t
                || m.strip_prefix(t.as_str())
                    .is_some_and(|r| r.starts_with('.'))
        })
    };
    // constructors and recursors print with their inductive
    let listed = |&(_, c): &(usize, NameId)| {
        !roots.contains(&c) && !matches!(env.consts[&c].kind, Kind::Ctor(_) | Kind::Rec(_))
    };
    let (hidden, shown): (Vec<_>, Vec<_>) = cone
        .iter()
        .copied()
        .filter(listed)
        .partition(|&(m, _)| trusted(m));
    let named = |pick: fn(&Kind) -> bool, all: bool| {
        let (mut names, mut more) = (Vec::new(), 0);
        for &(m, c) in &cone {
            if roots.contains(&c) || !pick(&env.consts[&c].kind) {
            } else if all || !trusted(m) {
                names.push(env.display(c));
            } else {
                more += 1;
            }
        }
        if more > 0 {
            names.push(format!("{more} more in {}", trust.join(", ")));
        }
        if names.is_empty() {
            "none".into()
        } else {
            names.join(", ")
        }
    };
    let axioms = named(|k| matches!(k, Kind::Axiom), true);
    let assumed = named(|k| matches!(k, Kind::Thm(_)), false);
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
    writeln!(
        out,
        "\n-- axioms: {axioms}\n-- theorems taken as stated: {assumed}"
    )?;
    let mut p = Printer::new(env, max);
    let mut lines = FxHashMap::default();
    let module: FxHashMap<NameId, usize> = cone.iter().map(|&(m, c)| (c, m)).collect();
    let roots = roots.iter().map(|&c| (module[&c], c));
    for (m, c) in roots.chain(shown) {
        let module = &env.modules[m];
        if let Entry::Vacant(e) = lines.entry(m) {
            e.insert(ranges(&resolve(search, module)?)?);
        }
        let file = format!("{}.lean", module.replace('.', "/"));
        let at = match lines[&m].get(&env.dotted(c)) {
            Some((a, b)) if a == b => format!("{file}:{a}"),
            Some((a, b)) => format!("{file}:{a}-{b}"),
            None => file,
        };
        writeln!(out, "\n-- {at}\n{}", p.decl(c))?;
    }
    Ok(())
}

/// The first and last source line of each declaration of a module, from `declRangeExt`.
fn ranges(path: &Path) -> Result<FxHashMap<String, (u64, u64)>> {
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
    /// The first component of every constant's name.
    heads: FxHashSet<NameId>,
}

/// Contexts, loosest first: a binder body, an arrow's domain, an application's argument.
const TOP: u8 = 0;
const DOMAIN: u8 = 1;
const ARG: u8 = 2;

/// A step of printing a term, kept on a stack since terms can be deeper than the call stack.
enum Step {
    Expr(ExprId, u8),
    Level(LevelId, bool),
    Text(Cow<'static, str>),
    /// The rest of a run of binders, ending at `sep` with the scope back at `depth`.
    Binders {
        e: ExprId,
        lam: bool,
        sep: &'static str,
        depth: usize,
    },
    Bind(String),
    Unbind(usize),
}

const fn text(s: &'static str) -> Step {
    Step::Text(Cow::Borrowed(s))
}

/// Push `items` to print in order, in parentheses if `on`.
fn emit<const N: usize>(todo: &mut Vec<Step>, on: bool, items: [Step; N]) {
    if on {
        todo.push(text(")"));
    }
    todo.extend(items.into_iter().rev());
    if on {
        todo.push(text("("));
    }
}

impl<'e> Printer<'e> {
    fn new(env: &'e Env, max: usize) -> Self {
        let mut heads = FxHashSet::default();
        for &c in env.consts.keys() {
            let mut n = c;
            while let Name::Str(p, _) | Name::Num(p, _) = env.names[n] {
                if p == ANON {
                    break;
                }
                n = p;
            }
            heads.insert(n);
        }
        Self {
            env,
            max,
            out: String::new(),
            scope: Vec::new(),
            loose: FxHashMap::default(),
            heads,
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
        self.scope.clear();
        let mut todo = vec![Step::Expr(e, TOP)];
        while let Some(step) = todo.pop() {
            if self.max > 0 && self.out.len() > self.max {
                break;
            }
            self.step(step, &mut todo);
        }
        let mut s = mem::take(&mut self.out);
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

    /// Print what `step` can at once, pushing the rest to `todo` in reverse.
    fn step(&mut self, step: Step, todo: &mut Vec<Step>) {
        let env = self.env;
        let depth = self.scope.len();
        match step {
            Step::Text(s) => self.out.push_str(&s),
            Step::Bind(x) => self.scope.push(x),
            Step::Unbind(d) => self.scope.truncate(d),
            Step::Level(l, arg) => self.level(l, arg, todo),
            Step::Binders { e, lam, sep, depth } => {
                let Some((n, ty, body, bi)) = self.binder(e, lam) else {
                    self.out.push_str(sep);
                    return emit(todo, false, [Step::Expr(e, TOP), Step::Unbind(depth)]);
                };
                let x = self.fresh(n);
                let (l, r) = match bi {
                    Binder::Default => ("(", ")"),
                    Binder::Implicit => ("{", "}"),
                    Binder::StrictImplicit => ("⦃", "⦄"),
                    Binder::InstImplicit => ("[", "]"),
                };
                write!(self.out, " {l}{x} : ").expect("string");
                let rest = Step::Binders {
                    e: body,
                    lam,
                    sep,
                    depth,
                };
                emit(
                    todo,
                    false,
                    [Step::Expr(ty, TOP), text(r), Step::Bind(x), rest],
                );
            }
            Step::Expr(e, prec) => match &env.exprs[e] {
                Expr::BVar(i) => {
                    match usize::try_from(*i)
                        .ok()
                        .and_then(|i| depth.checked_sub(i + 1))
                    {
                        Some(j) => self.out.push_str(&self.scope[j]),
                        None => write!(self.out, "#{i}").expect("string"),
                    }
                }
                Expr::Sort(l) => match env.levels[*l] {
                    Level::Zero => self.out.push_str("Prop"),
                    Level::Succ(u) if env.levels[u] == Level::Zero => self.out.push_str("Type"),
                    ref k => {
                        let (word, u) = match *k {
                            Level::Succ(u) => ("Type ", u),
                            _ => ("Sort ", *l),
                        };
                        emit(todo, prec >= ARG, [text(word), Step::Level(u, true)]);
                    }
                },
                Expr::Const(n, us) => {
                    self.out.push_str(&env.display(*n));
                    if let Some((first, rest)) = us.split_first() {
                        self.out.push_str(".{");
                        todo.push(text("}"));
                        for &u in rest.iter().rev() {
                            todo.extend([Step::Level(u, false), text(", ")]);
                        }
                        todo.push(Step::Level(*first, false));
                    }
                }
                Expr::App(..) => {
                    let on = prec >= ARG;
                    if on {
                        todo.push(text(")"));
                    }
                    let mut f = e;
                    while let Expr::App(g, a) = env.exprs[f] {
                        todo.extend([Step::Expr(a, ARG), text(" ")]);
                        f = g;
                    }
                    todo.push(Step::Expr(f, ARG));
                    if on {
                        todo.push(text("("));
                    }
                }
                Expr::Pi(_, ty, body, bi) if *bi == Binder::Default && self.range(*body) == 0 => {
                    let items = [
                        Step::Expr(*ty, DOMAIN),
                        text(" → "),
                        Step::Bind(String::new()),
                        Step::Expr(*body, TOP),
                        Step::Unbind(depth),
                    ];
                    emit(todo, prec > TOP, items);
                }
                Expr::Lam(..) | Expr::Pi(..) => {
                    let lam = matches!(env.exprs[e], Expr::Lam(..));
                    let (word, sep) = if lam { ("fun", " => ") } else { ("∀", ", ") };
                    emit(
                        todo,
                        prec > TOP,
                        [text(word), Step::Binders { e, lam, sep, depth }],
                    );
                }
                Expr::Let(n, ty, v, body) => {
                    let x = self.fresh(*n);
                    let items = [
                        Step::Text(format!("let {x} : ").into()),
                        Step::Expr(*ty, TOP),
                        text(" := "),
                        Step::Expr(*v, TOP),
                        text("; "),
                        Step::Bind(x),
                        Step::Expr(*body, TOP),
                        Step::Unbind(depth),
                    ];
                    emit(todo, prec > TOP, items);
                }
                Expr::Nat(n) => write!(self.out, "{n}").expect("string"),
                Expr::Str(s) => quote(&mut self.out, s),
                Expr::Proj(_, i, x) => {
                    todo.extend([
                        Step::Text(format!(".{}", i + 1).into()),
                        Step::Expr(*x, ARG),
                    ]);
                }
            },
        }
    }

    /// A universe, in parentheses if it is an `arg` of more than one token.
    fn level(&mut self, l: LevelId, arg: bool, todo: &mut Vec<Step>) {
        let env = self.env;
        let mut n = 0;
        let mut base = l;
        while let Level::Succ(u) = env.levels[base] {
            n += 1;
            base = u;
        }
        let plus = || Step::Text(format!(" + {n}").into());
        match env.levels[base] {
            Level::Zero => write!(self.out, "{n}").expect("string"),
            Level::Param(p) if n == 0 => self.out.push_str(&env.display(p)),
            Level::Param(p) => emit(todo, arg, [Step::Text(env.display(p).into()), plus()]),
            Level::Max(a, b) | Level::IMax(a, b) => {
                let word = if matches!(env.levels[base], Level::Max(..)) {
                    "max "
                } else {
                    "imax "
                };
                if n > 0 {
                    if arg {
                        todo.push(text(")"));
                    }
                    todo.push(plus());
                }
                let items = [
                    text(word),
                    Step::Level(a, true),
                    text(" "),
                    Step::Level(b, true),
                ];
                emit(todo, arg, items);
                if n > 0 && arg {
                    todo.push(text("("));
                }
            }
            Level::Succ(_) => unreachable!("peeled"),
        }
    }

    /// The binder at `e` if it continues a run of lambdas, or of dependent or non-default pis.
    fn binder(&mut self, e: ExprId, lam: bool) -> Option<(NameId, ExprId, ExprId, Binder)> {
        match self.env.exprs[e] {
            Expr::Lam(n, t, b, bi) if lam => Some((n, t, b, bi)),
            Expr::Pi(n, t, b, bi) if !lam && (bi != Binder::Default || self.range(b) > 0) => {
                Some((n, t, b, bi))
            }
            _ => None,
        }
    }

    /// One more than the largest loose bound variable of `e`, or 0 if it is closed.
    fn range(&mut self, e: ExprId) -> u64 {
        let mut todo = vec![(e, false)];
        while let Some((x, ready)) = todo.pop() {
            if self.loose.contains_key(&x) {
                continue;
            }
            let (subs, binds): (Vec<ExprId>, usize) = match self.env.exprs[x] {
                Expr::App(a, b) => (vec![a, b], 0),
                Expr::Lam(_, t, b, _) | Expr::Pi(_, t, b, _) => (vec![t, b], 1),
                Expr::Let(_, t, v, b) => (vec![t, v, b], 1),
                Expr::Proj(_, _, y) => (vec![y], 0),
                _ => (Vec::new(), 0),
            };
            if !ready && !subs.is_empty() {
                todo.push((x, true));
                todo.extend(subs.into_iter().map(|s| (s, false)));
                continue;
            }
            let last = subs.len().saturating_sub(binds);
            let r = match self.env.exprs[x] {
                Expr::BVar(i) => i + 1,
                _ => subs
                    .iter()
                    .enumerate()
                    .map(|(j, s)| {
                        let r = self.loose[s];
                        if j >= last {
                            r.saturating_sub(1)
                        } else {
                            r
                        }
                    })
                    .max()
                    .unwrap_or(0),
            };
            self.loose.insert(x, r);
        }
        self.loose[&e]
    }

    /// The binder's name without hygiene, as one component, distinct from every name in
    /// scope and from the first component of every constant, which it would shadow.
    fn fresh(&self, n: NameId) -> String {
        let env = self.env;
        let full = env.dotted(n);
        let base = full.split("._@").next().unwrap_or_default();
        let base = if base.is_empty() { "x" } else { base };
        let taken = |x: &str| {
            self.scope.iter().any(|s| *s == escape(x))
                || env
                    .names
                    .get(&Name::Str(ANON, x.into()))
                    .is_some_and(|h| self.heads.contains(&h))
        };
        let mut x = base.to_owned();
        let mut i = 1;
        while taken(&x) {
            x = format!("{base}_{i}");
            i += 1;
        }
        escape(&x).into_owned()
    }
}

/// `s` as a Lean string literal.
fn quote(q: &mut String, s: &str) {
    q.push('"');
    for c in s.chars() {
        match c {
            '"' => q.push_str("\\\""),
            '\\' => q.push_str("\\\\"),
            '\n' => q.push_str("\\n"),
            '\t' => q.push_str("\\t"),
            '\r' => q.push_str("\\r"),
            c if c.is_control() => write!(q, "\\x{:02x}", u32::from(c)).expect("string"),
            c => q.push(c),
        }
    }
    q.push('"');
}
