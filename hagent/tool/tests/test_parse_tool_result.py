# See LICENSE for details

from hagent.tool.parse_tool_result import (
    ParseSlangElabForLLM,
    ParseYosysVerilogElabForLLM,
    get_tool_result_parser,
)


# --- Sample slang log from a real elaboration failure ---
SLANG_LOG = """\
 Yosys 0.60+95 (git sha1 991e70489, g++ 15.2.0-4 -fPIC -O3)

1. Executing SLANG frontend.
/long/path/to/rtl_real_source/core/load_store_unit.sv:302:10: error: port 'satp_ppn_i' does not exist in 'cva6_mmu'
        .satp_ppn_i,
         ^
/long/path/to/rtl_real_source/core/load_store_unit.sv:303:10: error: port 'vsatp_ppn_i' does not exist in 'cva6_mmu'
        .vsatp_ppn_i,
         ^
/long/path/to/rtl_real_source/core/load_store_unit.sv:319:10: error: port 'req_port_i' does not exist in 'cva6_mmu'
        .req_port_i(dcache_req_ports_i[0]),
         ^
/long/path/to/rtl_real_source/core/load_store_unit.sv:320:10: error: port 'req_port_o' does not exist in 'cva6_mmu'
        .req_port_o(dcache_req_ports_o[0]),
         ^
/long/path/to/rtl_real_source/core/load_store_unit.sv:322:10: error: implicit named port 'pmpcfg_i' of type 'logic[7:0]' connects to value of inequivalent type 'pmpcfg_t[7:0]' [-Wimplicit-port-type-mismatch]
        .pmpcfg_i,
         ^~~~~~~~
/long/path/to/pipeline_output_dir/optimized/cva6_mmu.sv:112:29: error: use of undeclared identifier 'vs_asid_i'; did you mean 'vs_sum_i'?
assign itlb_lu_asid = v_i ? vs_asid_i : asid_i;
                            ^~~~~~~~~
/long/path/to/pipeline_output_dir/optimized/cva6_mmu.sv:46:17: note: declared here
    input logic vs_sum_i,
                ^
/long/path/to/pipeline_output_dir/optimized/cva6_mmu.sv:112:41: error: use of undeclared identifier 'asid_i'; did you mean 'vmid_i'?
assign itlb_lu_asid = v_i ? vs_asid_i : asid_i;
                                        ^~~~~~
/long/path/to/pipeline_output_dir/optimized/cva6_mmu.sv:135:19: note: declared here
  .lu_vmid_i     (vmid_i),
                  ^
fatal error: too many errors emitted, stopping now [--error-limit=]
"""


# --- Sample yosys read_verilog log ---
YOSYS_VERILOG_LOG = """\
 Yosys 0.60+95 (git sha1 991e70489, g++ 15.2.0-4 -fPIC -O3)

1. Executing Verilog-2005 frontend: /path/to/config_pkg.sv
Parsing SystemVerilog input from `/path/to/config_pkg.sv' to AST representation.
verilog frontend filename /path/to/config_pkg.sv
/path/to/config_pkg.sv:72: ERROR: syntax error, unexpected TOK_PACKAGESEP, expecting ',' or ';' or '='
"""


class TestParseSlangElabForLLM:
    def test_detect(self):
        assert ParseSlangElabForLLM.detect(SLANG_LOG) is True
        assert ParseSlangElabForLLM.detect('no slang here') is False

    def test_parse_diagnostics_count(self):
        p = ParseSlangElabForLLM()
        p.raw_text = SLANG_LOG
        assert p.parse() is True
        # 4 port-not-exist + 1 type-mismatch + 2 undeclared-id errors = 7 errors, 2 notes
        # "fatal error: too many errors" has no file:line:col, so it's not parsed (intentional)
        errors = [d for d in p.diagnostics if d.severity == 'error']
        notes = [d for d in p.diagnostics if d.severity == 'note']
        assert len(errors) == 7
        assert len(notes) == 2

    def test_parse_strips_paths_to_basename(self):
        p = ParseSlangElabForLLM()
        p.raw_text = SLANG_LOG
        p.parse()
        files = {d.file for d in p.diagnostics}
        # Should have basenames, not full paths
        assert 'load_store_unit.sv' in files
        assert 'cva6_mmu.sv' in files
        assert '/long/path' not in str(files)

    def test_format_for_llm_target_module(self):
        p = ParseSlangElabForLLM()
        p.raw_text = SLANG_LOG
        p.parse()
        output = p.format_for_llm(target_module='cva6_mmu')

        # Target module errors should be present with inline source
        assert 'cva6_mmu.sv:112:29' in output
        assert "use of undeclared identifier 'vs_asid_i'" in output

        # Other module errors should be grouped as missing ports
        assert 'Missing ports in cva6_mmu' in output
        assert 'satp_ppn_i' in output
        assert 'req_port_i' in output
        assert 'req_port_o' in output

        # Type mismatch should appear
        assert 'pmpcfg_i' in output

        # Should NOT contain full paths
        assert '/long/path/' not in output

        # Should NOT contain caret lines
        assert '^~~~~~~~~' not in output
        assert '^~~~~~~~' not in output

    def test_format_for_llm_includes_must_keep_ports_hint(self):
        p = ParseSlangElabForLLM()
        p.raw_text = SLANG_LOG
        p.parse()
        output = p.format_for_llm(target_module='cva6_mmu')
        assert 'MUST keep all original ports' in output

    def test_categorize_errors_slang(self):
        p = ParseSlangElabForLLM()
        p.raw_text = SLANG_LOG
        p.parse()
        cats = p.categorize_errors()

        # Should have: missing_port entries, undeclared_identifier entries, type_mismatch
        types = [c.error_type for c in cats]
        assert 'missing_port' in types
        assert 'undeclared_identifier' in types
        assert 'type_mismatch' in types

        # Check deduplication: 4 port-not-exist errors but each unique port
        missing = [c for c in cats if c.error_type == 'missing_port']
        assert len(missing) == 4  # satp_ppn_i, vsatp_ppn_i, req_port_i, req_port_o

        # Check undeclared identifiers
        undeclared = [c for c in cats if c.error_type == 'undeclared_identifier']
        assert len(undeclared) == 2  # vs_asid_i, asid_i

    def test_get_primary_error_type_slang(self):
        p = ParseSlangElabForLLM()
        p.raw_text = SLANG_LOG
        p.parse()
        # First error in the log is "port does not exist" → missing_port
        assert p.get_primary_error_type() == 'missing_port'

    def test_get_primary_error_type_empty(self):
        p = ParseSlangElabForLLM()
        p.raw_text = '1. Executing SLANG frontend.\n'
        p.parse()
        assert p.get_primary_error_type() == 'unknown'


class TestParseYosysVerilogElabForLLM:
    def test_detect(self):
        assert ParseYosysVerilogElabForLLM.detect(YOSYS_VERILOG_LOG) is True
        assert ParseYosysVerilogElabForLLM.detect(SLANG_LOG) is False

    def test_parse(self):
        p = ParseYosysVerilogElabForLLM()
        p.raw_text = YOSYS_VERILOG_LOG
        assert p.parse() is True
        assert len(p.diagnostics) == 1
        d = p.diagnostics[0]
        assert d.file == 'config_pkg.sv'
        assert d.line == 72
        assert 'syntax error' in d.message

    def test_format_for_llm(self):
        p = ParseYosysVerilogElabForLLM()
        p.raw_text = YOSYS_VERILOG_LOG
        p.parse()
        output = p.format_for_llm(target_module='cva6_mmu')
        assert 'config_pkg.sv:72' in output
        assert 'syntax error' in output

    def test_categorize_errors_yosys(self):
        p = ParseYosysVerilogElabForLLM()
        p.raw_text = YOSYS_VERILOG_LOG
        p.parse()
        cats = p.categorize_errors()
        assert len(cats) == 1
        assert cats[0].error_type == 'syntax_error'
        assert 'syntax error' in cats[0].context


class TestGetToolResultParser:
    def test_auto_detect_slang(self):
        parser = get_tool_result_parser(SLANG_LOG)
        assert parser is not None
        assert isinstance(parser, ParseSlangElabForLLM)

    def test_auto_detect_yosys_verilog(self):
        parser = get_tool_result_parser(YOSYS_VERILOG_LOG)
        assert parser is not None
        assert isinstance(parser, ParseYosysVerilogElabForLLM)

    def test_no_match(self):
        parser = get_tool_result_parser('just some random text with no tool markers')
        assert parser is None

    def test_load_from_file(self, tmp_path):
        log_file = tmp_path / 'elab.log'
        log_file.write_text(SLANG_LOG)
        parser = get_tool_result_parser(log_file)
        assert parser is not None
        assert isinstance(parser, ParseSlangElabForLLM)
        parser.parse()
        assert len(parser.diagnostics) > 0
