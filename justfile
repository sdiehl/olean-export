# Regenerate tests/cases/lean4export from the committed fixture oleans. lean4export must be
# built for the same Lean release as the fixtures.
lean4export bin="lean4export" toolchain="leanprover/lean4:v4.35.0-rc3":
    #!/usr/bin/env bash
    set -euo pipefail
    export LEAN_PATH=tests/cases/build:$(lean +{{toolchain}} --print-libdir)
    out=tests/cases/lean4export
    for m in Base Extra Top; do {{bin}} $m > $out/$m.ndjson; done
    {{bin}} Top -- Even.below.casesOn letty > $out/Top-cone.ndjson

# Rebuild the fixture oleans in tests/cases/build. Edited modules build from inside edit/, so
# that their private names match the originals.
fixtures toolchain="leanprover/lean4:v4.35.0-rc3":
    #!/usr/bin/env bash
    set -euo pipefail
    cd tests/cases
    lean() { command lean +{{toolchain}} "$@"; }
    mkdir -p build/edit
    for m in Base $(ls *.lean | sed 's/\.lean$//' | grep -vx Base); do
        LEAN_PATH=build lean -o build/$m.olean $m.lean
    done
    for f in edit/*.lean; do
        m=$(basename $f .lean)
        (cd edit && LEAN_PATH=../build lean -o ../build/edit/$m.olean $m.lean)
    done
    rm -f build/*.ir build/*.ir.sig build/edit/*.ir build/edit/*.ir.sig

# Check the statement cone of each fixture theorem with a kernel, theorems taken as axioms.
kernel checker="nl-fast":
    #!/usr/bin/env bash
    set -euo pipefail
    cargo build -q --release
    for c in Top:N.add_zero Top:letty Top:Even Pinned:pinned Pinned:shadow 'Pinned:«fun»'; do
        ./target/release/olean-export statement -L tests/cases/build -f ndjson \
            -c "${c#*:}" "${c%%:*}" | {{checker}} -
    done
