"""Curated catalog of RTL timing optimization techniques with before/after examples.

Each technique has a category name (prefixed with ``opt_``), a human-readable
description explaining *when* to apply it, and one or more block-level Verilog
snippet pairs showing the ill-formed (slow) pattern and the expert-optimized
result.

Use ``seed_db()`` to populate a :class:`FewShotMemory` instance so the LLM
can retrieve relevant examples via semantic similarity at optimization time.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Tuple

from hagent.tool.memory import OptimizationMemory, Memory_shot


@dataclass
class OptimizationTechnique:
    category: str  # ChromaDB error_type key, e.g. "opt_logic_duplication"
    name: str  # human-readable label
    description: str  # explains when this technique is suitable
    examples: List[Tuple[str, str]] = field(default_factory=list)  # (before, after)


# ---------------------------------------------------------------------------
# Technique definitions
# ---------------------------------------------------------------------------

TECHNIQUES: List[OptimizationTechnique] = [
    # ------------------------------------------------------------------
    # 1. Logic Duplication (Fanout Reduction)
    # ------------------------------------------------------------------
    OptimizationTechnique(
        category='opt_logic_duplication',
        name='Logic Duplication (Fanout Reduction)',
        description=(
            'Suitable when a single computed signal fans out to many consumers, '
            'creating a long wire delay or high-capacitance net. The fix is to '
            'duplicate the logic that generates the signal so each consumer (or '
            'small group) drives from its own local copy, reducing fanout and '
            'shortening the critical path.'
        ),
        examples=[
            (
                # BEFORE: shared_sel fans out to four muxes
                """\
// High-fanout select signal drives all output muxes
logic shared_sel;
assign shared_sel = (mode_a & flag_b) | (mode_c & flag_d);

always_comb begin
  out_w = shared_sel ? data_w1 : data_w0;
  out_x = shared_sel ? data_x1 : data_x0;
  out_y = shared_sel ? data_y1 : data_y0;
  out_z = shared_sel ? data_z1 : data_z0;
end""",
                # AFTER: each consumer gets a private copy of the select logic
                """\
// Duplicated select logic — each mux drives from a local copy
logic sel_w, sel_x, sel_y, sel_z;
assign sel_w = (mode_a & flag_b) | (mode_c & flag_d);
assign sel_x = (mode_a & flag_b) | (mode_c & flag_d);
assign sel_y = (mode_a & flag_b) | (mode_c & flag_d);
assign sel_z = (mode_a & flag_b) | (mode_c & flag_d);

always_comb begin
  out_w = sel_w ? data_w1 : data_w0;
  out_x = sel_x ? data_x1 : data_x0;
  out_y = sel_y ? data_y1 : data_y0;
  out_z = sel_z ? data_z1 : data_z0;
end""",
            ),
        ],
    ),
    # ------------------------------------------------------------------
    # 2. Critical Signal Isolation (Logic Promotion)
    # ------------------------------------------------------------------
    OptimizationTechnique(
        category='opt_critical_signal_isolation',
        name='Critical Signal Isolation (Logic Promotion)',
        description=(
            'Suitable when a timing-critical (late-arriving) signal is buried '
            'deep inside a chain of conditions or nested logic. The fix is to '
            'promote the critical signal to the outermost decision level and '
            'pre-compute the non-critical partial results, so the critical '
            'signal only passes through one level of logic before reaching '
            'the output.'
        ),
        examples=[
            (
                # BEFORE: critical late_valid buried after non-critical checks
                """\
// late_valid arrives late but is evaluated last in a nested chain
always_comb begin
  result = default_val;
  if (cfg_enable) begin
    if (addr_match) begin
      if (perm_ok) begin
        if (late_valid) begin  // <-- critical signal buried 4 levels deep
          result = fast_data;
        end
      end
    end
  end
end""",
                # AFTER: promote late_valid to top, pre-compute non-critical guard
                """\
// Pre-compute non-critical guard; critical late_valid at top level
logic non_crit_guard;
assign non_crit_guard = cfg_enable & addr_match & perm_ok;

always_comb begin
  if (late_valid)
    result = non_crit_guard ? fast_data : default_val;
  else
    result = default_val;
end""",
            ),
        ],
    ),
    # ------------------------------------------------------------------
    # 3. Shannon Expansion (Late Signal / Speculative Pre-computation)
    # ------------------------------------------------------------------
    OptimizationTechnique(
        category='opt_shannon_expansion',
        name='Shannon Expansion (Late Signal Technique)',
        description=(
            'Suitable when a late-arriving control signal selects between '
            'data paths that can be computed in advance. The fix is to '
            'pre-compute both possible outcomes (with the select assumed 0 '
            'and assumed 1), then use the late signal only for the final '
            'mux. This moves the late signal to the very last gate.'
        ),
        examples=[
            (
                # BEFORE: late_sel gates the computation
                """\
// late_sel arrives late and feeds into the ALU chain
always_comb begin
  if (late_sel) begin
    alu_a = src_a + offset_a;
    alu_b = src_b & mask_b;
  end else begin
    alu_a = src_a - offset_a;
    alu_b = src_b | mask_b;
  end
  result = alu_a ^ alu_b;
end""",
                # AFTER: pre-compute both arms, mux at the end with late_sel
                """\
// Shannon expansion: pre-compute both arms, mux with late signal
logic [WIDTH-1:0] alu_a_sel1, alu_b_sel1;
logic [WIDTH-1:0] alu_a_sel0, alu_b_sel0;
logic [WIDTH-1:0] result_sel1, result_sel0;

assign alu_a_sel1 = src_a + offset_a;
assign alu_b_sel1 = src_b & mask_b;
assign result_sel1 = alu_a_sel1 ^ alu_b_sel1;

assign alu_a_sel0 = src_a - offset_a;
assign alu_b_sel0 = src_b | mask_b;
assign result_sel0 = alu_a_sel0 ^ alu_b_sel0;

// Late signal only drives the final mux
assign result = late_sel ? result_sel1 : result_sel0;""",
            ),
        ],
    ),
    # ------------------------------------------------------------------
    # 4. Tree Decomposition / Balancing
    # ------------------------------------------------------------------
    OptimizationTechnique(
        category='opt_tree_balancing',
        name='Tree Decomposition (Balancing)',
        description=(
            'Suitable when logic is structured as a linear or cascading chain '
            '(e.g., a priority encoder, serial OR/AND reduction, or chained '
            'ternary mux). The critical-path depth grows as O(n). The fix is '
            'to restructure into a balanced binary tree so the depth becomes '
            'O(log n).'
        ),
        examples=[
            (
                # BEFORE: chained priority — linear depth
                """\
// Linear priority chain — depth grows with each entry
always_comb begin
  result = default_val;
  if (req[0])      result = data[0];
  else if (req[1]) result = data[1];
  else if (req[2]) result = data[2];
  else if (req[3]) result = data[3];
  else if (req[4]) result = data[4];
  else if (req[5]) result = data[5];
  else if (req[6]) result = data[6];
  else if (req[7]) result = data[7];
end""",
                # AFTER: balanced binary reduction tree
                """\
// Balanced binary tree — O(log n) depth
// Layer 1: pairwise selection
logic [WIDTH-1:0] win_01, win_23, win_45, win_67;
logic             any_01, any_23, any_45, any_67;

assign any_01 = req[0] | req[1];
assign win_01 = req[0] ? data[0] : data[1];
assign any_23 = req[2] | req[3];
assign win_23 = req[2] ? data[2] : data[3];
assign any_45 = req[4] | req[5];
assign win_45 = req[4] ? data[4] : data[5];
assign any_67 = req[6] | req[7];
assign win_67 = req[6] ? data[6] : data[7];

// Layer 2: quad selection
logic [WIDTH-1:0] win_0123, win_4567;
logic             any_0123, any_4567;

assign any_0123 = any_01 | any_23;
assign win_0123 = any_01 ? win_01 : win_23;
assign any_4567 = any_45 | any_67;
assign win_4567 = any_45 ? win_45 : win_67;

// Layer 3: final selection
assign result = any_0123 ? win_0123 : (any_4567 ? win_4567 : default_val);""",
            ),
        ],
    ),
]


def seed_db(memory: OptimizationMemory) -> int:
    """Populate *memory* with all curated optimization technique examples.

    Returns the number of examples inserted.
    """
    count = 0
    for tech in TECHNIQUES:
        for before, after in tech.examples:
            fix = Memory_shot(question=before, answer=after, description=tech.description)
            memory.add(category=tech.category, fix=fix, description=tech.description)
            count += 1
    return count
