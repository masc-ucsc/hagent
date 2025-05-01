#!/usr/bin/env python3
# See LICENSE for details

import re
from hagent.core.step import Step
from hagent.tool.chisel2v import Chisel2v

class Verify_candidate(Step):
    """
    Step that verifies a Chisel candidate by generating Verilog and checking basic validity.
    """
    def setup(self):
        super().setup()
        # Initialize Chisel2v tool
        self.c2v = Chisel2v()
        success = self.c2v.setup()
        if not success:
            raise ValueError(f"chisel2v setup failed: {self.c2v.error_message}")

    def _find_chisel_classname(self, chisel_code: str) -> str:
        # Try object Top extends App
        m = re.search(r'\bobject\s+(Top)\s+extends\s+App\b', chisel_code)
        if m:
            return m.group(1)
        # Try class Top extends Module
        m = re.search(r'\bclass\s+(Top)\s+extends\s+Module\b', chisel_code)
        if m:
            return m.group(1)
        # Fallback: first class extending Module
        m = re.search(r'\bclass\s+([A-Za-z0-9_]+)\s+extends\s+Module\b', chisel_code)
        return m.group(1) if m else ''

    def _run_chisel2v(self, chisel_code: str):
        if not chisel_code.strip():
            return False, None, 'Chisel snippet is empty'
        module_name = self._find_chisel_classname(chisel_code) or 'Top'
        try:
            verilog_out = self.c2v.generate_verilog(chisel_code, module_name)
            if 'module' not in verilog_out:
                return False, None, "Generated Verilog missing 'module' keyword."
            return True, verilog_out, ''
        except Exception as e:
            return False, None, str(e)

    def run(self, data):
        # Expect 'chisel_candidate' field from Apply_diff step
        chisel_updated = data.get('chisel_candidate', '')
        is_valid, verilog_candidate, error_msg = self._run_chisel2v(chisel_updated)

        # Attach verification result
        result = data.copy()
        result['verify_candidate'] = {
            'was_valid': is_valid,
            'verilog_candidate': verilog_candidate,
            'error_msg': error_msg
        }
        return result
