# See LICENSE for details

"""Tests for ExtractCriticalStep annotation methods."""

from pathlib import Path
from types import SimpleNamespace

import pytest

from hagent.workflow.frequency_opt.steps.extract_critical import ExtractCriticalStep

# ---------------------------------------------------------------------------
# Minimal netlist snippets extracted from a real synth.v
# Paths in (* src *) must be absolute (asserted by _extract_q_signal).
# ---------------------------------------------------------------------------

# Instance with no (* src *) annotation on the preceding line
NETLIST_NO_SRC = """\
  sky130_fd_sc_hd__dfxtp_1 _99999_ (
    .CLK(clock),
    .D(_00001_),
    .Q(\\some_module.some_signal )
  );
"""

# Minimal SV source for the top module — just module header + ports + endmodule.
# Enough for Compile_slang to parse ports. fu_data_i is on line 11.
MINIMAL_TOP_MODULE_SV = """\
module load_store_unit
  import ariane_pkg::*;
#(
    parameter type fu_data_t = logic
) (
    input logic clk_i,
    input logic rst_ni,
    input logic flush_i,
    input logic stall_st_pending_i,
    output logic no_st_pending_o,
    input fu_data_t fu_data_i,
    output logic lsu_ready_o
);
endmodule
"""

# Minimal SV source for a sub-module with mem_q as an internal register.
MINIMAL_LSU_BYPASS_SV = """\
module lsu_bypass (
    input logic clk_i,
    input logic rst_ni
);
    logic [127:0] mem_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) mem_q <= '0;
    end
endmodule
"""


def _make_netlist_single_bit(src_path: Path) -> str:
    """Instance _80159_: single-bit Q signal with (* src *) annotation."""
    return f"""\
  (* src = "{src_path / 'StageReg_2.sv'}:26.3" *)
  sky130_fd_sc_hd__dfxtp_1 _80159_ (
    .CLK(clock),
    .D(_58794_),
    .Q(\\pipeB_id_ex.reg_isValid )
  );
"""


def _make_netlist_bus_signal(src_path: Path) -> str:
    """Instance _79496_: bus Q signal with [63] index and (* src *) annotation."""
    return f"""\
  (* src = "{src_path / 'StageReg_6.sv'}:26.3" *)
  sky130_fd_sc_hd__dfxtp_1 _79496_ (
    .CLK(clock),
    .D(_58037_),
    .Q(\\pipeA_ex_mem.reg_nextpc [63])
  );
"""


def _make_netlist_dfrtp(src_path: Path) -> str:
    """Instance _105653_: dfrtp flop with bus Q signal and (* src *) annotation."""
    return f"""\
  (* src = "{src_path / 'lsu_bypass.sv'}:103.3" *)
  sky130_fd_sc_hd__dfrtp_1 _105653_ (
    .CLK(clk_i),
    .D(_071416_),
    .Q(\\lsu_bypass_i.mem_q [100]),
    .RESET_B(rst_ni)
  );
"""


def _make_netlist_bracketed_instance(src_path: Path) -> str:
    """Instance _200000_: Q signal with [N] in instance name (e.g. g_blocks[0])."""
    return f"""\
  (* src = "{src_path / 'fpnew_fma_multi.sv'}:42.3" *)
  sky130_fd_sc_hd__dfrtp_1 _200000_ (
    .CLK(clk_i),
    .D(_123456_),
    .Q(\\g_blocks[0].fpu_fpnew.control_U0.Sqrt_enable_SO [7]),
    .RESET_B(rst_ni)
  );
"""


# Minimal SV source for a deep sub-module with Sqrt_enable_SO as internal register.
MINIMAL_FPNEW_FMA_SV = """\
module fpnew_fma_multi (
    input logic clk_i,
    input logic rst_ni
);
    logic Sqrt_enable_SO;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) Sqrt_enable_SO <= '0;
    end
endmodule
"""


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _make_step(tmp_path: Path, netlist_text: str) -> ExtractCriticalStep:
    """Create an ExtractCriticalStep with a fake netlist_path for path resolution."""
    netlist_file = tmp_path / 'synth.v'
    netlist_file.write_text(netlist_text)
    step = ExtractCriticalStep.__new__(ExtractCriticalStep)
    step.netlist_path = netlist_file
    return step


def _make_step_with_annotation(tmp_path: Path, hierarchy: dict, design_top: str = 'load_store_unit') -> ExtractCriticalStep:
    """Create an ExtractCriticalStep wired up for annotation tests.

    Sets up:
      - step.storage.output_dir  ->  tmp_path / 'output'
      - step.locator.get_hierarchy()  ->  returns the given hierarchy dict
      - step.design.effective_synth_top  ->  design_top (used by _resolve_instance_signal)
    """
    output_dir = tmp_path / 'output'
    output_dir.mkdir()

    step = ExtractCriticalStep.__new__(ExtractCriticalStep)
    step.storage = SimpleNamespace(output_dir=str(output_dir))
    step.locator = SimpleNamespace(get_hierarchy=lambda: hierarchy)
    step.design = SimpleNamespace(effective_synth_top=design_top)
    step._annotation_offsets = {}
    return step


# ---------------------------------------------------------------------------
# Tests — _extract_q_signal
# ---------------------------------------------------------------------------


class TestExtractQSignal:
    """Tests for _extract_q_signal method."""

    def test_single_bit_signal_and_src(self, tmp_path):
        """Test extracting single-bit Q signal (pipeB_id_ex.reg_isValid) with src annotation."""
        src_path = tmp_path / 'rtl_source'
        src_path.mkdir()
        netlist = _make_netlist_single_bit(src_path)
        step = _make_step(tmp_path, netlist)
        signal, src_file, src_line = step._extract_q_signal(netlist, '_80159_')

        assert signal == 'pipeB_id_ex.reg_isValid'
        assert src_line == 26
        assert src_file is not None
        assert isinstance(src_file, Path)
        assert src_file.is_absolute()
        assert src_file.name == 'StageReg_2.sv'

    def test_bus_signal_and_src(self, tmp_path):
        """Test extracting bus Q signal (pipeA_ex_mem.reg_nextpc[63]) — index stripped."""
        src_path = tmp_path / 'rtl_source'
        src_path.mkdir()
        netlist = _make_netlist_bus_signal(src_path)
        step = _make_step(tmp_path, netlist)
        signal, src_file, src_line = step._extract_q_signal(netlist, '_79496_')

        assert signal == 'pipeA_ex_mem.reg_nextpc'
        assert src_line == 26
        assert src_file is not None
        assert isinstance(src_file, Path)
        assert src_file.is_absolute()
        assert src_file.name == 'StageReg_6.sv'

    def test_no_src_annotation_warns(self, tmp_path, capsys):
        """When (* src = "..." *) is missing, src_file and src_line should be None."""
        step = _make_step(tmp_path, NETLIST_NO_SRC)
        signal, src_file, src_line = step._extract_q_signal(NETLIST_NO_SRC, '_99999_')

        assert signal == 'some_module.some_signal'
        assert src_file is None
        assert src_line is None
        captured = capsys.readouterr()
        assert 'Warning' in captured.out
        assert '_99999_' in captured.out

    def test_instance_not_found_raises(self, tmp_path):
        """Non-existent instance name should raise RuntimeError."""
        src_path = tmp_path / 'rtl_source'
        src_path.mkdir()
        netlist = _make_netlist_single_bit(src_path)
        step = _make_step(tmp_path, netlist)
        with pytest.raises(RuntimeError, match='not found in netlist'):
            step._extract_q_signal(netlist, '_00000_')

    def test_src_path_is_absolute(self, tmp_path):
        """The src_file should be an absolute Path from the (* src *) annotation."""
        src_path = tmp_path / 'rtl_source'
        src_path.mkdir()
        netlist = _make_netlist_single_bit(src_path)
        step = _make_step(tmp_path, netlist)
        _, src_file, _ = step._extract_q_signal(netlist, '_80159_')

        assert src_file is not None
        assert isinstance(src_file, Path)
        assert src_file.is_absolute()
        assert src_file.name == 'StageReg_2.sv'


# ---------------------------------------------------------------------------
# Tests — _annotate_module_port  (external input/output port)
# ---------------------------------------------------------------------------


class TestAnnotateModulePort:
    """Tests for _annotate_module_port using Compile_slang."""

    def test_external_input_port(self, tmp_path):
        """Annotate fu_data_i in the module port list via Compile_slang."""
        sv_file = tmp_path / 'load_store_unit.sv'
        sv_file.write_text(MINIMAL_TOP_MODULE_SV)

        hierarchy = {
            'top': {'module': 'load_store_unit', 'file': str(sv_file)},
        }
        step = _make_step_with_annotation(tmp_path, hierarchy)

        step._annotate_module_port('load_store_unit', 'fu_data_i', 'the starting external input port of the critical path')

        annotated = (tmp_path / 'output' / 'annotated_rtl' / 'load_store_unit.sv').read_text()
        lines = annotated.splitlines()

        crit_idx = next(i for i, ln in enumerate(lines) if '// CRITICAL:' in ln)
        assert 'fu_data_i' in lines[crit_idx]
        assert 'starting external input port' in lines[crit_idx]
        # The actual declaration should be on the very next line
        assert 'fu_data_i' in lines[crit_idx + 1]
        assert 'input' in lines[crit_idx + 1]

    def test_port_not_found_warns(self, tmp_path, capsys):
        """Non-existent port name should print a warning and not create a file."""
        sv_file = tmp_path / 'load_store_unit.sv'
        sv_file.write_text(MINIMAL_TOP_MODULE_SV)

        hierarchy = {
            'top': {'module': 'load_store_unit', 'file': str(sv_file)},
        }
        step = _make_step_with_annotation(tmp_path, hierarchy)

        step._annotate_module_port('load_store_unit', 'nonexistent_port_i', 'test')

        captured = capsys.readouterr()
        assert 'Warning' in captured.out
        assert 'nonexistent_port_i' in captured.out


# ---------------------------------------------------------------------------
# Tests — _annotate_instance_module  (capture D flop / hierarchical signal)
# ---------------------------------------------------------------------------


class TestAnnotateInstanceModule:
    """Tests for _annotate_instance_module (hierarchy-based annotation)."""

    def test_capture_flop_signal(self, tmp_path):
        """Annotate mem_q (internal register) in lsu_bypass module via hierarchy lookup."""
        sv_file = tmp_path / 'lsu_bypass.sv'
        sv_file.write_text(MINIMAL_LSU_BYPASS_SV)

        hierarchy = {
            'load_store_unit': {'module': 'load_store_unit', 'file': str(tmp_path / 'load_store_unit.sv')},
            'load_store_unit.lsu_bypass_i': {'module': 'lsu_bypass', 'file': str(sv_file)},
        }
        step = _make_step_with_annotation(tmp_path, hierarchy)

        step._annotate_instance_module('lsu_bypass_i.mem_q', 'the ending flop of the critical path', src_line=5)

        annotated = (tmp_path / 'output' / 'annotated_rtl' / 'lsu_bypass.sv').read_text()
        lines = annotated.splitlines()

        crit_idx = next(i for i, ln in enumerate(lines) if '// CRITICAL:' in ln)
        assert 'mem_q' in lines[crit_idx]
        assert 'ending flop' in lines[crit_idx]
        # The declaration line should be right after the annotation
        assert 'mem_q' in lines[crit_idx + 1]

    def test_instance_not_found_warns(self, tmp_path, capsys):
        """Unknown instance name should print a warning."""
        hierarchy = {}
        step = _make_step_with_annotation(tmp_path, hierarchy)

        step._annotate_instance_module('nonexistent_i.some_signal', 'test')

        captured = capsys.readouterr()
        assert 'Warning' in captured.out
        assert 'not found in hierarchy' in captured.out

    def test_no_hierarchy_warns(self, tmp_path, capsys):
        """Signal with no dot should warn about missing hierarchy."""
        hierarchy = {}
        step = _make_step_with_annotation(tmp_path, hierarchy)

        step._annotate_instance_module('bare_signal', 'test')

        captured = capsys.readouterr()
        assert 'Warning' in captured.out
        assert 'no hierarchy' in captured.out

    def test_complex_hierarchy_with_brackets(self, tmp_path):
        """Annotate signal in a deep hierarchy where instance names contain [N]."""
        sv_file = tmp_path / 'fpnew_fma_multi.sv'
        sv_file.write_text(MINIMAL_FPNEW_FMA_SV)

        hierarchy = {
            'VX_core_top': {'module': 'VX_core_top', 'file': str(tmp_path / 'VX_core_top.sv')},
            'VX_core_top.core': {'module': 'VX_core', 'file': str(tmp_path / 'VX_core.sv')},
            'VX_core_top.core.execute': {'module': 'VX_execute', 'file': str(tmp_path / 'VX_execute.sv')},
            'VX_core_top.core.execute.fpu_unit': {'module': 'VX_fpu_unit', 'file': str(tmp_path / 'VX_fpu_unit.sv')},
            'VX_core_top.core.execute.fpu_unit.g_blocks[0]': {
                'module': 'VX_fpu_block',
                'file': str(tmp_path / 'VX_fpu_block.sv'),
            },
            'VX_core_top.core.execute.fpu_unit.g_blocks[0].fpu_fpnew': {
                'module': 'fpnew_top',
                'file': str(tmp_path / 'fpnew_top.sv'),
            },
            'VX_core_top.core.execute.fpu_unit.g_blocks[0].fpu_fpnew.control_U0': {
                'module': 'fpnew_fma_multi',
                'file': str(sv_file),
            },
        }
        step = _make_step_with_annotation(
            tmp_path,
            hierarchy,
            design_top='VX_fpu_unit$VX_core_top.core.execute.fpu_unit',
        )

        step._annotate_instance_module(
            'g_blocks[0].fpu_fpnew.control_U0.Sqrt_enable_SO',
            'the ending flop of the critical path',
            src_line=5,
        )

        annotated = (tmp_path / 'output' / 'annotated_rtl' / 'fpnew_fma_multi.sv').read_text()
        lines = annotated.splitlines()

        crit_idx = next(i for i, ln in enumerate(lines) if '// CRITICAL:' in ln)
        assert 'Sqrt_enable_SO' in lines[crit_idx]
        assert 'ending flop' in lines[crit_idx]
        assert 'Sqrt_enable_SO' in lines[crit_idx + 1]

    def test_src_line_skips_earlier_mention(self, tmp_path):
        """src_line targets the declaration, not an earlier mention of the signal."""
        # mem_q appears on line 3 (comment) and line 7 (declaration).
        # With src_line=7, annotation should go before line 7, not line 3.
        sv_content = """\
module lsu_bypass (
    input logic clk_i,
    input logic rst_ni  // mem_q is documented here
);
    logic [63:0] other_reg;
    logic [31:0] unrelated;
    logic [127:0] mem_q;
    always_ff @(posedge clk_i) begin
        mem_q <= '0;
    end
endmodule
"""
        sv_file = tmp_path / 'lsu_bypass.sv'
        sv_file.write_text(sv_content)

        hierarchy = {
            'load_store_unit': {'module': 'load_store_unit', 'file': str(tmp_path / 'top.sv')},
            'load_store_unit.lsu_bypass_i': {'module': 'lsu_bypass', 'file': str(sv_file)},
        }
        step = _make_step_with_annotation(tmp_path, hierarchy)

        step._annotate_instance_module('lsu_bypass_i.mem_q', 'the ending flop', src_line=7)

        annotated = (tmp_path / 'output' / 'annotated_rtl' / 'lsu_bypass.sv').read_text()
        lines = annotated.splitlines()

        crit_idx = next(i for i, ln in enumerate(lines) if '// CRITICAL:' in ln)
        # Annotation should be right before 'logic [127:0] mem_q;' (originally line 7)
        assert 'mem_q' in lines[crit_idx]
        assert 'logic [127:0] mem_q' in lines[crit_idx + 1]
        # Should NOT be before the comment on line 3
        assert crit_idx > 3

    def test_two_annotations_same_file(self, tmp_path):
        """Two annotations in the same file: offsets tracked so both land correctly."""
        sv_content = """\
module lsu_bypass (
    input logic clk_i,
    input logic rst_ni
);
    logic [63:0] other_reg;
    logic [127:0] mem_q;
    always_ff @(posedge clk_i) begin
        other_reg <= '0;
        mem_q <= '0;
    end
endmodule
"""
        sv_file = tmp_path / 'lsu_bypass.sv'
        sv_file.write_text(sv_content)

        hierarchy = {
            'load_store_unit': {'module': 'load_store_unit', 'file': str(tmp_path / 'top.sv')},
            'load_store_unit.lsu_bypass_i': {'module': 'lsu_bypass', 'file': str(sv_file)},
        }
        step = _make_step_with_annotation(tmp_path, hierarchy)

        # First annotation at line 5 (other_reg), second at line 6 (mem_q)
        step._annotate_instance_module('lsu_bypass_i.other_reg', 'launch flop', src_line=5)
        step._annotate_instance_module('lsu_bypass_i.mem_q', 'capture flop', src_line=6)

        annotated = (tmp_path / 'output' / 'annotated_rtl' / 'lsu_bypass.sv').read_text()
        lines = annotated.splitlines()

        # Both annotations should be present
        crit_lines = [i for i, ln in enumerate(lines) if '// CRITICAL:' in ln]
        assert len(crit_lines) == 2

        # First annotation before other_reg declaration
        assert 'other_reg' in lines[crit_lines[0]]
        assert 'other_reg' in lines[crit_lines[0] + 1]
        # Second annotation before mem_q declaration
        assert 'mem_q' in lines[crit_lines[1]]
        assert 'mem_q' in lines[crit_lines[1] + 1]


# ---------------------------------------------------------------------------
# Tests — _extract_q_signal with intermediate brackets
# ---------------------------------------------------------------------------


class TestExtractQSignalBrackets:
    """Tests for _extract_q_signal preserving intermediate [N] brackets."""

    def test_preserves_intermediate_brackets(self, tmp_path):
        """Instance names with [N] (g_blocks[0]) must be preserved; only trailing [7] stripped."""
        src_path = tmp_path / 'rtl_source'
        src_path.mkdir()
        netlist = _make_netlist_bracketed_instance(src_path)
        step = _make_step(tmp_path, netlist)
        signal, src_file, src_line = step._extract_q_signal(netlist, '_200000_')

        assert signal == 'g_blocks[0].fpu_fpnew.control_U0.Sqrt_enable_SO'
        assert src_line == 42
        assert src_file is not None
        assert src_file.name == 'fpnew_fma_multi.sv'
