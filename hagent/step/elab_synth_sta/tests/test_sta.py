# See LICENSE for details

import tempfile
from pathlib import Path

import pytest

from hagent.step.elab_synth_sta.sta import Sta


class TestStaValidation:
    def _make_step(self, tmp_path, data):
        step = Sta()
        step.output_file = str(tmp_path / 'output.yaml')
        step.overwrite_conf = data
        step.setup()
        return step

    def test_missing_design_info(self, tmp_path):
        with pytest.raises(ValueError, match='design_info'):
            self._make_step(tmp_path, {'rtl': {'source_dir': '/tmp'}, 'storage': {'output_dir': '/tmp/out'}})

    def test_missing_storage_output_dir(self, tmp_path):
        with pytest.raises(ValueError, match='storage'):
            self._make_step(
                tmp_path,
                {
                    'design_info': {'top_module': 'ALU'},
                    'rtl': {'source_dir': '/tmp'},
                    'storage': {},
                },
            )

    def test_missing_netlist_file(self, tmp_path):
        with pytest.raises(ValueError, match='rtl.netlist_file'):
            self._make_step(
                tmp_path,
                {
                    'design_info': {'top_module': 'ALU'},
                    'storage': {'output_dir': str(tmp_path / 'out')},
                    'rtl': {'source_dir': str(tmp_path)},
                },
            )

    def test_netlist_file_not_found(self, tmp_path):
        step = self._make_step(
            tmp_path,
            {
                'design_info': {'top_module': 'ALU'},
                'storage': {'output_dir': str(tmp_path / 'out')},
                'rtl': {'netlist_file': '/nonexistent/synth.v', 'source_dir': str(tmp_path)},
            },
        )
        with pytest.raises(ValueError, match='Synthesized netlist not found'):
            step.run(step.input_data)


class TestTimingParsing:
    def test_parse_timing_log_with_clock(self):
        step = Sta()
        step.output_file = '/dev/null'
        step.input_data = {}

        sta_content = """Startpoint: _reg1_ (rising edge-triggered flip-flop clocked by clk)
Endpoint: _reg2_ (rising edge-triggered flip-flop clocked by clk)
Path Group: clk
Path Type: max

  Delay    Time   Description
---------------------------------------------------------
   0.00    0.00   clock clk (rise edge)
   0.10    0.10 ^ _reg1_/CK (DFFX1)
   0.50    0.60 v _logic_/Y (INVX1)
   1.40    2.00 ^ _reg2_/D (DFFX1)
           2.00   data arrival time

  10.00   10.00   clock clk (rise edge)
  -0.10    9.90   clock uncertainty
   0.00    9.90   clock reconvergence pessimism
  -0.05    9.85 ^ _reg2_/CK (DFFX1)
           9.85   data required time
---------------------------------------------------------
           9.85   data required time
          -2.00   data arrival time
---------------------------------------------------------
           7.85   slack (MET)
"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.log', delete=False) as f:
            f.write(sta_content)
            log_path = Path(f.name)

        try:
            freq = step._parse_timing_log(log_path, 'clk')
            assert freq == pytest.approx(500.0)  # 1000 / 2.0 = 500 MHz
        finally:
            log_path.unlink()

    def test_parse_timing_log_no_clock(self):
        step = Sta()
        step.output_file = '/dev/null'
        step.input_data = {}

        freq = step._parse_timing_log(Path('/nonexistent'), None)
        assert freq == float('inf')

    def test_parse_timing_log_no_match(self):
        step = Sta()
        step.output_file = '/dev/null'
        step.input_data = {}

        with tempfile.NamedTemporaryFile(mode='w', suffix='.log', delete=False) as f:
            f.write('No timing data here\n')
            log_path = Path(f.name)

        try:
            freq = step._parse_timing_log(log_path, 'clk')
            assert freq == float('inf')
        finally:
            log_path.unlink()

    def test_parse_timing_log_wrong_path_group(self):
        step = Sta()
        step.output_file = '/dev/null'
        step.input_data = {}

        sta_content = """Startpoint: _reg1_
Path Group: async_default
Path Type: max

           5.00   data arrival time
"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.log', delete=False) as f:
            f.write(sta_content)
            log_path = Path(f.name)

        try:
            freq = step._parse_timing_log(log_path, 'clk')
            assert freq == float('inf')  # clk group not found
        finally:
            log_path.unlink()
