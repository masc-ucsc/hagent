# See LICENSE for details
"""Unit tests for VerilogPatchApplier."""

import pytest

from hagent.tool.verilog_patch_applier import PatchBlock, VerilogPatchApplier


@pytest.fixture
def applier():
    return VerilogPatchApplier()


# ── parse_patches ────────────────────────────────────────────────────────────


class TestParsing:
    def test_single_block(self, applier):
        resp = 'Here is the fix:\n<<<<<<< SEARCH\nresult <= a + b;\n=======\nresult <= sum_pre;\n>>>>>>> REPLACE\n'
        patches = applier.parse_patches(resp)
        assert len(patches) == 1
        assert patches[0].search == 'result <= a + b;'
        assert patches[0].replace == 'result <= sum_pre;'

    def test_multiple_blocks(self, applier):
        resp = (
            '<<<<<<< SEARCH\n'
            'line_a\n'
            '=======\n'
            'line_a_new\n'
            '>>>>>>> REPLACE\n'
            '\n'
            '<<<<<<< SEARCH\n'
            'line_b\n'
            '=======\n'
            'line_b_new\n'
            '>>>>>>> REPLACE\n'
            '\n'
            '<<<<<<< SEARCH\n'
            'line_c\n'
            '=======\n'
            'line_c_new\n'
            '>>>>>>> REPLACE\n'
        )
        patches = applier.parse_patches(resp)
        assert len(patches) == 3
        assert patches[0].search == 'line_a'
        assert patches[1].search == 'line_b'
        assert patches[2].search == 'line_c'

    def test_blocks_inside_markdown_fence(self, applier):
        resp = '```verilog\n<<<<<<< SEARCH\nold_line\n=======\nnew_line\n>>>>>>> REPLACE\n```\n'
        patches = applier.parse_patches(resp)
        assert len(patches) == 1
        assert patches[0].search == 'old_line'

    def test_no_blocks(self, applier):
        resp = 'module foo; endmodule'
        assert applier.parse_patches(resp) == []

    def test_malformed_block_missing_separator(self, applier):
        resp = '<<<<<<< SEARCH\nold_line\nnew_line\n>>>>>>> REPLACE\n'
        # Missing ======= separator, should not parse
        assert applier.parse_patches(resp) == []

    def test_empty_replace(self, applier):
        resp = '<<<<<<< SEARCH\ndelete_me;\n=======\n\n>>>>>>> REPLACE\n'
        patches = applier.parse_patches(resp)
        assert len(patches) == 1
        assert patches[0].search == 'delete_me;'
        # replace may be empty or just whitespace
        assert patches[0].replace.strip() == ''

    def test_multiline_search_and_replace(self, applier):
        resp = (
            '<<<<<<< SEARCH\n'
            '  always @(posedge clk) begin\n'
            '    result <= a + b;\n'
            '  end\n'
            '=======\n'
            '  always @(posedge clk) begin\n'
            '    result <= sum_pre;\n'
            '  end\n'
            '>>>>>>> REPLACE\n'
        )
        patches = applier.parse_patches(resp)
        assert len(patches) == 1
        assert 'result <= a + b;' in patches[0].search
        assert 'result <= sum_pre;' in patches[0].replace


# ── _normalize_verilog_line ──────────────────────────────────────────────────


class TestNormalization:
    def test_whitespace_collapse(self, applier):
        line = '  result   <=   a +  b ;  '
        normalized = applier._normalize_verilog_line(line)
        assert 'result' in normalized
        assert '  ' not in normalized  # no double spaces

    def test_operators(self, applier):
        line = 'a<=b==c!=d===e!==f>=g'
        normalized = applier._normalize_verilog_line(line)
        assert ' <= ' in normalized
        assert ' == ' in normalized
        assert ' != ' in normalized
        assert ' === ' in normalized
        assert ' !== ' in normalized
        assert ' >= ' in normalized

    def test_comments_preserved(self, applier):
        line = 'result <= a + b; // critical path'
        normalized = applier._normalize_verilog_line(line)
        assert '// critical path' in normalized

    def test_punctuation(self, applier):
        line = 'assign out = mux ( sel , a , b ) ;'
        normalized = applier._normalize_verilog_line(line)
        # Should have normalized spacing
        assert '  ' not in normalized


# ── apply_patches ────────────────────────────────────────────────────────────


class TestApply:
    SIMPLE_MODULE = (
        'module test(input clk, input [7:0] a, b, output reg [7:0] result);\n'
        '  always @(posedge clk) begin\n'
        '    result <= a + b;\n'
        '  end\n'
        'endmodule'
    )

    def test_exact_match(self, applier):
        patch = PatchBlock(
            search='    result <= a + b;',
            replace='    result <= sum_pre;',
            raw_block='',
        )
        result = applier.apply_patches(self.SIMPLE_MODULE, [patch])
        assert 'result <= sum_pre;' in result
        assert 'result <= a + b;' not in result

    def test_whitespace_flexible_match(self, applier):
        """SEARCH has different spacing than original, should still match."""
        patch = PatchBlock(
            search='result  <=  a + b ;',
            replace='    result <= sum_pre;',
            raw_block='',
        )
        result = applier.apply_patches(self.SIMPLE_MODULE, [patch])
        assert 'sum_pre' in result

    def test_multiple_patches_sequential(self, applier):
        code = (
            'module test(input clk, input [7:0] a, b, output reg [7:0] result);\n'
            '  wire [7:0] tmp;\n'
            '  assign tmp = a & b;\n'
            '  always @(posedge clk) begin\n'
            '    result <= a + b;\n'
            '  end\n'
            'endmodule'
        )
        patches = [
            PatchBlock(search='  assign tmp = a & b;', replace='  assign tmp = a | b;', raw_block=''),
            PatchBlock(search='    result <= a + b;', replace='    result <= tmp;', raw_block=''),
        ]
        result = applier.apply_patches(code, patches)
        assert 'assign tmp = a | b;' in result
        assert 'result <= tmp;' in result

    def test_indentation_preservation(self, applier):
        """SEARCH has no indent, but code has 4-space indent."""
        patch = PatchBlock(
            search='result <= a + b;',
            replace='result <= sum_pre;  // optimized',
            raw_block='',
        )
        result = applier.apply_patches(self.SIMPLE_MODULE, [patch])
        # The replacement should be re-indented to match the original 4-space indent
        for line in result.splitlines():
            if 'sum_pre' in line:
                assert line.startswith('    '), f'Expected 4-space indent, got: {line!r}'

    def test_search_not_found_raises(self, applier):
        patch = PatchBlock(
            search='this line does not exist in the code',
            replace='replacement',
            raw_block='',
        )
        with pytest.raises(RuntimeError, match='SEARCH block not found'):
            applier.apply_patches(self.SIMPLE_MODULE, [patch])

    def test_deletion(self, applier):
        """Empty REPLACE effectively deletes the matched lines."""
        code = 'module test;\n  wire unused;\n  wire used;\nendmodule'
        patch = PatchBlock(search='  wire unused;', replace='', raw_block='')
        result = applier.apply_patches(code, [patch])
        assert 'unused' not in result
        assert 'wire used;' in result

    def test_insertion_via_context(self, applier):
        """Insert new lines by including a context line in both SEARCH and REPLACE."""
        code = 'module test;\n  always @(posedge clk) begin\n    result <= a + b;\n  end\nendmodule'
        patch = PatchBlock(
            search='  always @(posedge clk) begin',
            replace=('  wire [31:0] pre_sum;\n  assign pre_sum = a + b;\n  always @(posedge clk) begin'),
            raw_block='',
        )
        result = applier.apply_patches(code, [patch])
        assert 'wire [31:0] pre_sum;' in result
        assert 'assign pre_sum = a + b;' in result
        assert 'always @(posedge clk) begin' in result

    def test_comment_only_search_block(self, applier):
        """SEARCH block containing only comments should still match."""
        code = (
            'module lsu(input clk, input [7:0] a);\n'
            '  // ------------------------\n'
            '  // Misaligned Exception\n'
            '  // ------------------------\n'
            '  // we can detect a misaligned exception immediately\n'
            '  always_comb begin : data_misaligned_detection\n'
            "    data_misaligned = 1'b0;\n"
            '  end\n'
            'endmodule'
        )
        patch = PatchBlock(
            search=(
                '  // ------------------------\n'
                '  // Misaligned Exception\n'
                '  // ------------------------\n'
                '  // we can detect a misaligned exception immediately'
            ),
            replace=(
                '  // ------------------------\n'
                '  // Misaligned Exception\n'
                '  // ------------------------\n'
                '  // predecode op classes\n'
                '  logic op_is_word;\n'
                '  logic misalign_word;\n'
                '  // we can detect a misaligned exception immediately'
            ),
            raw_block='',
        )
        result = applier.apply_patches(code, [patch])
        assert 'logic op_is_word;' in result
        assert 'logic misalign_word;' in result
        assert '// Misaligned Exception' in result
        assert 'data_misaligned' in result

    def test_comment_only_search_with_code_patch(self, applier):
        """Two patches: first is comment-only SEARCH, second is code SEARCH."""
        code = (
            'module lsu(input clk);\n'
            '  // Misaligned Exception\n'
            '  // we can detect a misaligned exception immediately\n'
            '  always_comb begin\n'
            "    data_misaligned = 1'b0;\n"
            '    if (valid) begin\n'
            "      if (vaddr[1:0] != 2'b00) data_misaligned = 1'b1;\n"
            '    end\n'
            '  end\n'
            'endmodule'
        )
        patches = [
            PatchBlock(
                search='  // Misaligned Exception\n  // we can detect a misaligned exception immediately',
                replace='  // Misaligned Exception\n  logic op_is_word;\n  // we can detect a misaligned exception immediately',
                raw_block='',
            ),
            PatchBlock(
                search="      if (vaddr[1:0] != 2'b00) data_misaligned = 1'b1;",
                replace="    op_is_word = 1'b1;\n    data_misaligned = op_is_word & (vaddr[1:0] != 2'b00);",
                raw_block='',
            ),
        ]
        result = applier.apply_patches(code, patches)
        assert 'logic op_is_word;' in result
        assert 'op_is_word & ' in result


# ── try_apply ────────────────────────────────────────────────────────────────


class TestTryApply:
    def test_success(self, applier):
        code = 'module m;\n  wire a;\nendmodule'
        resp = '<<<<<<< SEARCH\n  wire a;\n=======\n  wire b;\n>>>>>>> REPLACE\n'
        result = applier.try_apply(code, resp)
        assert result is not None
        assert 'wire b;' in result

    def test_no_patches_returns_none(self, applier):
        code = 'module m;\nendmodule'
        resp = 'No changes needed.'
        assert applier.try_apply(code, resp) is None

    def test_failed_application_raises(self, applier):
        code = 'module m;\nendmodule'
        resp = '<<<<<<< SEARCH\nnonexistent line\n=======\nreplacement\n>>>>>>> REPLACE\n'
        with pytest.raises(RuntimeError):
            applier.try_apply(code, resp)


# ── Realistic end-to-end test ────────────────────────────────────────────────


class TestRealistic:
    def test_timing_optimization_patches(self, applier):
        original = (
            'module alu(\n'
            '  input  wire        clk,\n'
            '  input  wire [31:0] operand_a,\n'
            '  input  wire [31:0] operand_b,\n'
            '  input  wire [3:0]  op_code,\n'
            '  output reg  [31:0] result\n'
            ');\n'
            '  always @(posedge clk) begin\n'
            '    case (op_code)\n'
            "      4'b0000: result <= operand_a + operand_b;  // CRITICAL: add\n"
            "      4'b0001: result <= operand_a - operand_b;\n"
            "      default: result <= 32'b0;\n"
            '    endcase\n'
            '  end\n'
            'endmodule'
        )

        llm_response = (
            'I will pre-compute the addition to break the critical path:\n\n'
            '<<<<<<< SEARCH\n'
            '  always @(posedge clk) begin\n'
            '=======\n'
            '  // Pre-compute addition\n'
            '  wire [31:0] pre_sum;\n'
            '  assign pre_sum = operand_a + operand_b;\n'
            '\n'
            '  always @(posedge clk) begin\n'
            '>>>>>>> REPLACE\n'
            '\n'
            '<<<<<<< SEARCH\n'
            "      4'b0000: result <= operand_a + operand_b;  // CRITICAL: add\n"
            '=======\n'
            "      4'b0000: result <= pre_sum;  // pre-computed sum\n"
            '>>>>>>> REPLACE\n'
        )

        result = applier.try_apply(original, llm_response)
        assert result is not None
        assert 'wire [31:0] pre_sum;' in result
        assert 'assign pre_sum = operand_a + operand_b;' in result
        assert 'result <= pre_sum;' in result
        # Original critical line should be replaced
        assert 'result <= operand_a + operand_b;' not in result
        # Non-critical lines should be untouched
        assert 'result <= operand_a - operand_b;' in result
        # Module structure preserved
        assert result.strip().startswith('module alu')
        assert result.strip().endswith('endmodule')


# ── diagnose_format ────────────────────────────────────────────────────────────


class TestDiagnoseFormat:
    def test_wrong_closing_end(self, applier):
        resp = '<<<<<<< SEARCH\nold line\n=======\nnew line\n>>>>>>> END\n'
        diag = applier.diagnose_format(resp)
        assert diag is not None
        assert 'REPLACE' in diag
        assert 'END' in diag

    def test_wrong_closing_done(self, applier):
        resp = '<<<<<<< SEARCH\nold\n=======\nnew\n>>>>>>> DONE\n'
        diag = applier.diagnose_format(resp)
        assert diag is not None
        assert 'REPLACE' in diag

    def test_missing_closing(self, applier):
        resp = '<<<<<<< SEARCH\nold\n=======\nnew\n'
        diag = applier.diagnose_format(resp)
        assert diag is not None

    def test_valid_format_returns_none(self, applier):
        resp = '<<<<<<< SEARCH\nold\n=======\nnew\n>>>>>>> REPLACE\n'
        diag = applier.diagnose_format(resp)
        assert diag is None

    def test_no_markers_returns_none(self, applier):
        resp = 'module foo; endmodule'
        diag = applier.diagnose_format(resp)
        assert diag is None

    def test_empty_returns_none(self, applier):
        diag = applier.diagnose_format('')
        assert diag is None

    def test_inside_markdown_fence(self, applier):
        resp = '```verilog\n<<<<<<< SEARCH\nold\n=======\nnew\n>>>>>>> END\n```\n'
        diag = applier.diagnose_format(resp)
        assert diag is not None
        assert 'REPLACE' in diag

    def test_multiple_wrong_closings(self, applier):
        resp = (
            '<<<<<<< SEARCH\nold1\n=======\nnew1\n>>>>>>> END\n\n'
            '<<<<<<< SEARCH\nold2\n=======\nnew2\n>>>>>>> DONE\n'
        )
        diag = applier.diagnose_format(resp)
        assert diag is not None
        assert 'REPLACE' in diag

    def test_search_without_separator(self, applier):
        """SEARCH and REPLACE markers but no ======= separator."""
        resp = '<<<<<<< SEARCH\nold\nnew\n>>>>>>> REPLACE\n'
        # parse_patches won't match (no separator), so this is a format issue
        diag = applier.diagnose_format(resp)
        assert diag is not None
        assert '=======' in diag or 'separator' in diag.lower()

    def test_realistic_wrong_end_marker(self, applier):
        """Real-world case: large Verilog patch with >>>>>>> END instead of REPLACE."""
        resp = (
            '<<<<<<< SEARCH\n'
            '  assign vaddr_xlen = $unsigned($signed(fu_data_i.imm) + $signed(fu_data_i.operand_a));\n'
            '  assign vaddr_i = vaddr_xlen[CVA6Cfg.VLEN-1:0];\n'
            '  assign overflow = (CVA6Cfg.IS_XLEN64 && (!((&vaddr_xlen[CVA6Cfg.XLEN-1:CVA6Cfg.SV-1]) == 1\'b1'
            ' || (|vaddr_xlen[CVA6Cfg.XLEN-1:CVA6Cfg.SV-1]) == 1\'b0)));\n'
            '=======\n'
            '  assign vaddr_xlen = $unsigned($signed(fu_data_i.imm) + $signed(fu_data_i.operand_a));\n'
            '  assign vaddr_i = vaddr_xlen[CVA6Cfg.VLEN-1:0];\n'
            '  localparam int UPPER_W = CVA6Cfg.XLEN - (CVA6Cfg.SV - 1);\n'
            '  logic [UPPER_W-1:0] vaddr_upper;\n'
            '  assign vaddr_upper = vaddr_xlen[CVA6Cfg.XLEN-1:CVA6Cfg.SV-1];\n'
            '  assign overflow = (CVA6Cfg.IS_XLEN64 && !((&vaddr_upper) || (~|vaddr_upper)));\n'
            '>>>>>>> END\n'
        )
        diag = applier.diagnose_format(resp)
        assert diag is not None
        assert 'REPLACE' in diag
        assert 'END' in diag
