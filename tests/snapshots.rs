use std::{fmt::Write as _, path::PathBuf};
use tiny_olean::{Env, Exporter};

fn build() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases/build")
}

#[test]
fn export() {
    let build = build();
    insta::glob!("cases/*.lean", |path| {
        let module = path.file_stem().unwrap().to_str().unwrap();
        let env = Env::load(std::slice::from_ref(&build), &[module]).unwrap();
        let mut ex = Exporter::new(&env, Vec::new());
        ex.meta().unwrap();
        ex.all().unwrap();
        insta::assert_snapshot!(String::from_utf8(ex.finish().unwrap()).unwrap());
    });
}

#[test]
fn damaged() {
    let top = std::fs::read(build().join("Top.olean")).unwrap();
    let mut future = top.clone();
    future[7..13].copy_from_slice(b"4.99.0");
    let cases: [(&str, Vec<u8>); 3] = [
        ("truncated", top[..top.len() / 2].to_vec()),
        ("future", future),
        ("garbage", b"not an olean at all".repeat(8)),
    ];
    let dir = std::env::temp_dir().join(format!("tiny-olean-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::copy(build().join("Base.olean"), dir.join("Base.olean")).unwrap();
    let mut out = String::new();
    for (name, bytes) in cases {
        std::fs::write(dir.join("Top.olean"), bytes).unwrap();
        let err = Env::load(std::slice::from_ref(&dir), &["Top"]).unwrap_err();
        let msg = err.to_string().replace(dir.to_str().unwrap(), "$DIR");
        writeln!(out, "{name}: {:?}: {msg}", err.kind()).unwrap();
    }
    std::fs::remove_dir_all(&dir).unwrap();
    insta::assert_snapshot!(out);
}
