use olean_export::{Env, Exporter};
use std::{env, fmt::Write as _, fs, path::PathBuf, process, slice};

fn build() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")
}

#[test]
fn export() {
    let build = build();
    insta::glob!("cases/*.lean", |path| {
        let module = path.file_stem().unwrap().to_str().unwrap();
        let env = Env::load(slice::from_ref(&build), &[module]).unwrap();
        let mut ex = Exporter::new(&env, Vec::new());
        ex.meta().unwrap();
        ex.all().unwrap();
        let out = String::from_utf8(ex.finish().unwrap()).unwrap();
        insta::assert_snapshot!(out.replace(env!("CARGO_PKG_VERSION"), "[version]"));
    });
}

#[test]
fn damaged() {
    let top = fs::read(build().join("Top.olean")).unwrap();
    let mut future = top.clone();
    future[7..13].copy_from_slice(b"4.99.0");
    let cases: [(&str, Vec<u8>); 3] = [
        ("truncated", top[..top.len() / 2].to_vec()),
        ("future", future),
        ("garbage", b"not an olean at all".repeat(8)),
    ];
    let dir = env::temp_dir().join(format!("olean-export-{}", process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::copy(build().join("Base.olean"), dir.join("Base.olean")).unwrap();
    let mut out = String::new();
    for (name, bytes) in cases {
        fs::write(dir.join("Top.olean"), bytes).unwrap();
        let err = Env::load(slice::from_ref(&dir), &["Top"]).unwrap_err();
        let msg = err.to_string().replace(dir.to_str().unwrap(), "$DIR");
        writeln!(out, "{name}: {msg}").unwrap();
    }
    fs::remove_dir_all(&dir).unwrap();
    insta::assert_snapshot!(out);
}

/// The statement report, and the cone of its first root exported with theorems as axioms.
#[test]
fn statement() {
    let build = build();
    let search = slice::from_ref(&build);
    let mut out = String::new();
    for (module, consts) in [
        ("Top", &["N.add_zero", "letty", "Even"][..]),
        ("Extra", &["greeting", "twice"]),
        ("Pinned", &["pinned", "shadow"]),
    ] {
        let env = Env::load_statements(search, &[module], 1, &|_, _| {}).unwrap();
        let roots: Vec<_> = consts.iter().map(|c| env.find_name(c).unwrap()).collect();
        let mut text = Vec::new();
        olean_export::statement::report(&env, search, &roots, &["Init".into()], 0, &mut text)
            .unwrap();
        writeln!(out, "{}", String::from_utf8(text).unwrap()).unwrap();
        if module != "Extra" {
            let mut ex = Exporter::new(&env, Vec::new()).statements();
            for (_, c) in env.statement(&roots[..1]).unwrap() {
                ex.constant(c).unwrap();
            }
            let ndjson = String::from_utf8(ex.finish().unwrap()).unwrap();
            let kinds = ndjson.lines().filter_map(|l| {
                ["axiom", "def", "thm", "inductive"]
                    .into_iter()
                    .find(|k| l.starts_with(&format!("{{\"{k}\"")))
            });
            writeln!(out, "exported: {}", kinds.collect::<Vec<_>>().join(", ")).unwrap();
        }
    }
    insta::assert_snapshot!(out);
}
