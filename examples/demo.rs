#![allow(clippy::many_single_char_names)]

use std::path::PathBuf;
use tiny_olean::{Env, Expr, Kind, Level};

fn level(env: &Env, l: u32) -> String {
    match env.levels[l] {
        Level::Zero => "0".into(),
        Level::Succ(a) => format!("{}+1", level(env, a)),
        Level::Max(a, b) => format!("max {} {}", level(env, a), level(env, b)),
        Level::IMax(a, b) => format!("imax {} {}", level(env, a), level(env, b)),
        Level::Param(n) => env.display(n),
    }
}

fn sort(env: &Env, l: u32) -> String {
    match env.levels[l] {
        Level::Zero => "Prop".into(),
        Level::Succ(a) if env.levels[a] == Level::Zero => "Type".into(),
        Level::Succ(a) => format!("Type {}", level(env, a)),
        _ => format!("Sort ({})", level(env, l)),
    }
}

fn binder(env: &Env, n: u32, depth: usize) -> String {
    let s = env.display(n);
    let s = s.split("._@").next().unwrap_or_default();
    format!("{s}{depth}")
}

fn expr(env: &Env, e: u32, ctx: &mut Vec<String>) -> String {
    match &env.exprs[e] {
        Expr::BVar(i) => ctx[ctx.len() - 1 - usize::try_from(*i).unwrap()].clone(),
        Expr::Sort(l) => sort(env, *l),
        Expr::Const(n, _) => env.display(*n),
        Expr::App(f, a) => {
            let a = expr(env, *a, ctx);
            let a = if a.contains(' ') { format!("({a})") } else { a };
            format!("{} {a}", expr(env, *f, ctx))
        }
        Expr::Lam(n, t, b, _) | Expr::Pi(n, t, b, _) => {
            let ty = expr(env, *t, ctx);
            ctx.push(binder(env, *n, ctx.len()));
            let body = expr(env, *b, ctx);
            let x = ctx.pop().unwrap();
            let head = if matches!(env.exprs[e], Expr::Lam(..)) {
                "fun"
            } else {
                "forall"
            };
            format!("{head} ({x} : {ty}), {body}")
        }
        Expr::Let(n, t, v, b) => {
            let (ty, val) = (expr(env, *t, ctx), expr(env, *v, ctx));
            ctx.push(binder(env, *n, ctx.len()));
            let body = expr(env, *b, ctx);
            format!("let {} : {ty} := {val}; {body}", ctx.pop().unwrap())
        }
        Expr::Nat(v) => v.to_string(),
        Expr::Str(v) => format!("{v:?}"),
        Expr::Proj(_, i, x) => format!("({}).{}", expr(env, *x, ctx), i + 1),
    }
}

fn main() {
    let build = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build");
    let env = Env::load(&[build], &["Top"]).expect("load fixture oleans");
    println!(
        "loaded {} from Lean {}",
        env.modules.join(" + "),
        env.header.version
    );
    println!(
        "{} constants ({} unsafe skipped), {} names, {} levels, {} expressions\n",
        env.consts.len(),
        env.skipped,
        env.names.len(),
        env.levels.len(),
        env.exprs.len()
    );
    for name in [
        "N",
        "N.add",
        "N.add_zero",
        "Pair.swap",
        "Quot.lift",
        "Even",
        "letty",
    ] {
        let k = &env.consts[&env.find_name(name).unwrap()];
        let ty = expr(&env, k.ty, &mut Vec::new());
        match &k.kind {
            Kind::Defn { value, .. } | Kind::Thm { value, .. } => {
                println!(
                    "{name} : {ty}\n  := {}\n",
                    expr(&env, *value, &mut Vec::new())
                );
            }
            Kind::Induct { ctors, .. } => {
                let cs: Vec<String> = ctors.iter().map(|&c| env.display(c)).collect();
                println!("{name} : {ty}\n  ctors {}\n", cs.join(", "));
            }
            _ => println!("{name} : {ty}\n"),
        }
    }
}
