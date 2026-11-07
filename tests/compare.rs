use olean_export::{blean::Blean, compare, Env, Exporter, Sink};
use std::path::PathBuf;

fn cases() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases")
}

fn export<S: Sink>(env: &Env, sink: S, consts: &[&str]) -> S::Output {
    let mut ex = Exporter::with_sink(env, sink);
    ex.meta().unwrap();
    if consts.is_empty() {
        ex.all().unwrap();
    }
    for c in consts {
        ex.constant(env.find_name(c).unwrap()).unwrap();
    }
    ex.finish().unwrap()
}

/// Every fixture, and one constant subset, against what lean4export wrote for it (`just
/// lean4export`).
#[test]
fn matches_lean4export() {
    let build = cases().join("build");
    let runs: [(&str, &str, &[&str]); 4] = [
        ("Base", "Base", &[]),
        ("Extra", "Extra", &[]),
        ("Top", "Top", &[]),
        ("Top", "Top-cone", &["Even.below.casesOn", "letty"]),
    ];
    for (module, file, consts) in runs {
        let want = std::fs::read(cases().join(format!("lean4export/{file}.ndjson"))).unwrap();
        let search = std::slice::from_ref(&build);
        let env = if consts.is_empty() {
            Env::load(search, &[module]).unwrap()
        } else {
            Env::load_cone(search, &[module], consts, 1, &|_, _| {}).unwrap()
        };
        let ndjson = export(&env, olean_export::ndjson::Ndjson::new(Vec::new()), consts);
        let blean = export(&env, Blean::new(Vec::new()), consts);
        for got in [ndjson, blean] {
            let d = compare(&want, &got).unwrap();
            assert!(d.is_empty() && d.decls.0 > 0, "{file}: {d:?}");
        }
    }
}

#[test]
fn reports_differences() {
    let dir = cases().join("lean4export");
    let top = std::fs::read(dir.join("Top.ndjson")).unwrap();
    let cone = std::fs::read(dir.join("Top-cone.ndjson")).unwrap();
    let d = compare(&top, &cone).unwrap();
    assert!(!d.only_a.is_empty() && d.only_b.is_empty() && d.differ.is_empty());
}
