FROM mascucsc/hagent-builder:latest

ENV CHIPYARD_DIR=/chipyard \
    DEBIAN_FRONTEND=noninteractive

WORKDIR /

# -----------------------------------------------------------------------------
# Stage 1 — clone chipyard with submodules, verify tree.
# -----------------------------------------------------------------------------
RUN git clone --depth=1 --recurse-submodules --shallow-submodules \
      https://github.com/ucb-bar/chipyard.git $CHIPYARD_DIR \
 && echo "[verify] chipyard tree + submodules" \
 && test -f $CHIPYARD_DIR/env.sh                     || { echo "FAIL: no env.sh";       exit 1; } \
 && test -f $CHIPYARD_DIR/build-setup.sh             || { echo "FAIL: no build-setup"; exit 1; } \
 && test -d $CHIPYARD_DIR/generators/boom/src        || { echo "FAIL: boom submodule missing"; exit 1; } \
 && test -d $CHIPYARD_DIR/generators/rocket-chip/src || { echo "FAIL: rocket-chip submodule missing"; exit 1; }

WORKDIR $CHIPYARD_DIR

# -----------------------------------------------------------------------------
# Stage 2 — build-setup (toolchain skipped; builder has JDK/sbt/firtool/verilator).
# No '|| true' — any failure here must stop the image build.
# -----------------------------------------------------------------------------
RUN ./build-setup.sh --skip-toolchain --skip-marshal -s 6 -s 7 -s 8 -s 9 \
 && echo "[verify] env.sh sourceable + sbt/firtool reachable" \
 && bash -lc "source env.sh && command -v sbt && command -v firtool" \
      || { echo "FAIL: build-setup incomplete"; exit 1; }

# -----------------------------------------------------------------------------
# Stage 3 — pre-generate SmallBoomConfig (MiniBOOM).
# -----------------------------------------------------------------------------
RUN bash -lc "source env.sh && \
      cd sims/verilator && \
      make verilog CONFIG=SmallBoomConfig SUB_PROJECT=boom -j$(nproc)" \
 && echo "[verify] SmallBoomConfig .sv exists and non-empty" \
 && SM=$(ls $CHIPYARD_DIR/sims/verilator/generated-src/*SmallBoomConfig*/*.sv 2>/dev/null | head -1) \
 && test -n "$SM" && test -s "$SM" \
      || { echo "FAIL: no SmallBoomConfig .sv produced"; exit 1; } \
 && echo "[verify] SmallBoom top .sv = $SM ($(wc -l < $SM) lines)"

# -----------------------------------------------------------------------------
# Stage 4 — pre-generate MegaBoomConfig.
# Separate layer: if this fails, SmallBoom is still cached and reusable.
# -----------------------------------------------------------------------------
RUN bash -lc "source env.sh && \
      cd sims/verilator && \
      make verilog CONFIG=MegaBoomConfig SUB_PROJECT=boom -j$(nproc)" \
 && echo "[verify] MegaBoomConfig .sv exists and non-empty" \
 && MG=$(ls $CHIPYARD_DIR/sims/verilator/generated-src/*MegaBoomConfig*/*.sv 2>/dev/null | head -1) \
 && test -n "$MG" && test -s "$MG" \
      || { echo "FAIL: no MegaBoomConfig .sv produced"; exit 1; } \
 && echo "[verify] MegaBoom top .sv = $MG ($(wc -l < $MG) lines)"

WORKDIR $CHIPYARD_DIR
CMD ["/bin/bash", "-l"]
