# Regenerate tests/cases/lean4export from the committed fixture oleans. lean4export must be
# built for the same Lean release as the fixtures.
lean4export bin="lean4export" toolchain="leanprover/lean4:v4.35.0-rc3":
    #!/usr/bin/env bash
    set -euo pipefail
    export LEAN_PATH=tests/cases/build:$(lean +{{toolchain}} --print-libdir)
    out=tests/cases/lean4export
    for m in Base Extra Top; do {{bin}} $m > $out/$m.ndjson; done
    {{bin}} Top -- Even.below.casesOn letty > $out/Top-cone.ndjson
