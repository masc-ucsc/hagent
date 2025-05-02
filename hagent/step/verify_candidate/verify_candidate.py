#!/usr/bin/env python3
# See LICENSE for details

import sys
from hagent.core.step import Step
from hagent.tool.chisel2v import Chisel2v

class Verify_candidate(Step):
    """
    Compiles a Chisel snippet to Verilog and verifies it contains a module.
    Reads from:
      - chisel_candidate: str
    Emits:
      - was_valid: bool
      - verilog_candidate: str or None
      - error_msg: str
    """
    def setup(self):
        super().setup()
        self.setup_called = True

    def run(self, data):
        chisel_code = data.get('chisel_candidate', '')
        if not chisel_code.strip():
            data['was_valid'] = False
            data['verilog_candidate'] = None
            data['error_msg'] = 'Chisel snippet is empty'
            return data

        c2v = Chisel2v()
        if not c2v.setup():
            data['was_valid'] = False
            data['verilog_candidate'] = None
            data['error_msg'] = 'chisel2v setup failed: ' + c2v.error_message
            return data

        # Allow overriding module name if provided; default to Top
        module_name = data.get('module_name') or 'Top'

        try:
            verilog_out = c2v.generate_verilog(chisel_code, module_name)
            if 'module' not in verilog_out:
                data['was_valid'] = False
                data['verilog_candidate'] = None
                data['error_msg'] = "Generated Verilog missing 'module' keyword."
            else:
                data['was_valid'] = True
                data['verilog_candidate'] = verilog_out
                data['error_msg'] = ''
        except Exception as e:
            err = str(e)
            if "error during sbt launcher" in err:
                print("sbt run does not seem to work")
                print(err)
                sys.exit(3)
            data['was_valid'] = False
            data['verilog_candidate'] = None
            data['error_msg'] = err

        return data
