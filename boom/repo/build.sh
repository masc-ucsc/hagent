#!/usr/bin/env bash
# Run on kaffirlime (not mada4). Logs to build.log in cwd.
# Each stage checks the previous one and bails on failure.
set -euo pipefail

cd "$(dirname "$0")"
export DOCKER_BUILDKIT=1

say() { printf '\n[hagent-boom] %s\n' "$*"; }
die() { printf '\n[hagent-boom] FAIL: %s\n' "$*" >&2; exit 1; }

# -----------------------------------------------------------------------------
# Step 1 — pull base builder image, verify it is pullable
# -----------------------------------------------------------------------------
say "step 1/4: pulling mascucsc/hagent-builder:latest"
docker pull mascucsc/hagent-builder:latest
docker image inspect mascucsc/hagent-builder:latest >/dev/null \
  || die "base image not present after pull"
say "step 1/4 OK"

# -----------------------------------------------------------------------------
# Step 2 — build image (per-stage checks live inside the Dockerfile)
# -----------------------------------------------------------------------------
say "step 2/4: building mascucsc/hagent-boom:latest  (expect ~1.5-2.5 h)"
docker build -t mascucsc/hagent-boom:latest . 2>&1 | tee build.log
docker image inspect mascucsc/hagent-boom:latest >/dev/null \
  || die "image did not materialise"
say "step 2/4 OK  (image built)"

# -----------------------------------------------------------------------------
# Step 3 — smoke test: both configs must have real Verilog inside the image
# -----------------------------------------------------------------------------
say "step 3/4: smoke test both MiniBOOM and MegaBOOM artifacts"
docker run --rm mascucsc/hagent-boom:latest bash -lc '
  set -e
  for CFG in SmallBoomConfig MegaBoomConfig; do
    F=$(ls /chipyard/sims/verilator/generated-src/*${CFG}*/*.sv 2>/dev/null | head -1)
    if [ -z "$F" ] || [ ! -s "$F" ]; then
      echo "SMOKE FAIL: $CFG missing or empty"; exit 1
    fi
    echo "SMOKE OK: $CFG -> $F ($(wc -l < $F) lines)"
  done
' | tee smoke_test.log
grep -q "^SMOKE OK: SmallBoomConfig" smoke_test.log || die "SmallBoomConfig smoke failed"
grep -q "^SMOKE OK: MegaBoomConfig"  smoke_test.log || die "MegaBoomConfig smoke failed"
say "step 3/4 OK"

# -----------------------------------------------------------------------------
# Step 4 — summarise. Do NOT push; that is a separate manual step.
# -----------------------------------------------------------------------------
say "step 4/4: summary"
docker images mascucsc/hagent-boom:latest
printf '\nTo push after review:\n  docker login -u mascucsc\n  docker push mascucsc/hagent-boom:latest\n'
