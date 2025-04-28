import os
from hagent.core.step import Step
from hagent.tool.chisel2v import Chisel2v
from hagent.tool.equiv_check import Equiv_check

class Verify_candidate(Step):
    """
    Compiles Chisel code to Verilog and runs a logic equivalence check against a fixed Verilog.

    Reads from:
      - chisel_candidate: str
      - verilog_fixed: str
    Emits:
      - was_valid: bool
      - verilog_candidate: str or None
      - compile_error: str or None
      - lec_error: str or None
    """
    def setup(self):
        super().setup()
        # Setup Chisel-to-Verilog compiler
        self.compiler = Chisel2v()
        if not self.compiler.setup():
            raise ValueError(f"Compile_slang setup failed: {self.compiler.error_message}")
        # Setup equivalence checker
        self.eq = Equiv_check()
        if not self.eq.setup():
            # Store setup error, but allow run to proceed
            self.eq_error = self.eq.get_error() or 'Equiv_check setup failed'
        else:
            self.eq_error = None
        self.setup_called = True

    def run(self, data):
        chisel_code = data.get('chisel_candidate', '')
        verilog_fixed = data.get('verilog_fixed', '')
        result = {
            'was_valid': False,
            'verilog_candidate': None,
            'compile_error': None,
            'lec_error': None,
        }
        # Compile step
        try:
            verilog_out = self.compiler.generate_verilog(chisel_code, 'Top')
            if 'module' not in verilog_out:
                raise RuntimeError("Generated Verilog missing 'module' keyword.")
            result['verilog_candidate'] = verilog_out
        except Exception as e:
            result['compile_error'] = str(e)
            data.update(result)
            return data

        # Equivalence check step
        if not verilog_fixed.strip():
            result['lec_error'] = 'No verilog_fixed provided'
            data.update(result)
            return data

        if self.eq_error:
            result['lec_error'] = self.eq_error
            data.update(result)
            return data

        try:
            is_equiv = self.eq.check_equivalence(verilog_fixed, verilog_out)
            if is_equiv is True:
                result['was_valid'] = True
            else:
                result['lec_error'] = self.eq.get_error() or 'LEC failed'
        except Exception as e:
            result['lec_error'] = str(e)

        data.update(result)
        return data
