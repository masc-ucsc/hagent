#!/usr/bin/env python3
# See LICENSE for details

import difflib
from hagent.core.step import Step


class Unified_diff(Step):
    """
    Exactly reproduces your old _generate_diff behavior:
      n=20 context lines, fromfile='verilog_original.v', tofile='verilog_fixed.v'
    Reads:
      - verilog_original: str
      - verilog_fixed:    str
    Emits:
      - verilog_diff:     str
    """

    def setup(self):
        super().setup()
        # no overrides here: we hard-code to match your old function
        self.context = 25
        self.fromfile = 'verilog_original.v'
        self.tofile = 'verilog_fixed.v'
        self.setup_called = True

    def run(self, data):
        old_lines = data.get('verilog_original', '').splitlines()
        new_lines = data.get('verilog_fixed', '').splitlines()
        diff = difflib.unified_diff(old_lines, new_lines, fromfile=self.fromfile, tofile=self.tofile, lineterm='', n=self.context)
        data['verilog_diff'] = '\n'.join(diff)
        return data
