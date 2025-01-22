import os
import re
import subprocess
import tempfile
from typing import Optional


class Equiv_check:
    """
    Equiv_check verifies logical equivalence of two Verilog designs using Yosys.

    This class attempts two approaches:
      1) Standard 'equiv -assert'
      2) An SMT-based check
    """

    def __init__(self):
        """
        Initializes the Equiv_check object:
         - yosys_installed: indicates if Yosys is available.
         - error_message: stores any error encountered.
         - equivalence_check_result: last known equivalence outcome (True/False/None).
         - counterexample_info: stores counterexample details if available.
         - timeout_seconds: defaults to 60s for Yosys calls.
         - working_dir: subdirectory to store all temporary files.
        """
        self.yosys_installed = False
        self.error_message = ''
        self.equivalence_check_result: Optional[bool] = None
        self.counterexample_info: Optional[str] = None
        self.timeout_seconds = 60

        # Create a subdirectory for working files
        self.working_dir = os.path.join(os.getcwd(), 'equiv_check')
        os.makedirs(self.working_dir, exist_ok=True)

    def setup(self, yosys_path: Optional[str] = None) -> bool:
        """
        Checks if Yosys is installed and accessible. If yosys_path is provided,
        use that binary instead of relying on system PATH.

        Returns True if Yosys is available, False otherwise.
        """
        if yosys_path:
            command = [yosys_path, '-V']
        else:
            command = ['yosys', '-V']

        try:
            subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
            self.yosys_installed = True
            return True
        except (subprocess.CalledProcessError, FileNotFoundError) as e:
            self.yosys_installed = False
            self.error_message = f'Yosys not found or not accessible: {e}'
            return False

    def check_equivalence(self, gold_code: str, reference_code: str) -> Optional[bool]:
        """
        Checks the equivalence of two Verilog designs:
          - gold_code:   The 'gold' version to match
          - gate_code: The 'gate' version

        Both must define exactly one module each. If either file defines more or zero modules,
        we raise an exception. We rename the gold top to 'gold', and the gate top to 'gate'.

        Returns:
            True if designs are equivalent,
            False if designs are not equivalent,
            None if unknown (error or timeout).
        """
        if not self.yosys_installed:
            raise RuntimeError('Yosys not installed or setup() not called.')

        # Extract module names
        gold_top = self._extract_single_module_name(gold_code)
        ref_top = self._extract_single_module_name(reference_code)

        # Write each Verilog code to a temporary file
        gold_path = self._write_temp_verilog(gold_code, 'gold')
        ref_path = self._write_temp_verilog(reference_code, 'gate')

        # 1) Run the standard equivalence method
        code_equiv, out_equiv, err_equiv = self._run_equiv_method(gold_path, ref_path, gold_top, ref_top)
        # Decide if method 1 concluded
        method1_result = self._analyze_yosys_result(code_equiv, out_equiv, err_equiv, method='equiv')

        if method1_result is not None:
            # either True or False or known error => done
            self.equivalence_check_result = method1_result
            return self.equivalence_check_result

        # 2) If method 1 was inconclusive, try SMT-based approach
        code_smt, out_smt, err_smt = self._run_smt_method(gold_path, ref_path, gold_top, ref_top)
        method2_result = self._analyze_yosys_result(code_smt, out_smt, err_smt, method='smt')

        self.equivalence_check_result = method2_result
        return self.equivalence_check_result

    def get_error(self) -> str:
        """Returns the error message if any."""
        return self.error_message

    def get_counterexample(self) -> Optional[str]:
        """Returns the stored counterexample information if available."""
        return self.counterexample_info

    # ------------------- Internal Helpers -------------------

    def _extract_single_module_name(self, verilog_code: str) -> str:
        """
        Extracts exactly one module name from the verilog_code. If there are multiple or none,
        raises a ValueError.
        """
        # A simple regex to match `module <name> (`
        # Allows optional spaces and either ( or ;
        pattern = r'^\s*module\s+([A-Za-z0-9_]+)\s*(?:\(|;)'
        matches = re.findall(pattern, verilog_code, flags=re.MULTILINE)
        if len(matches) == 0:
            raise ValueError("No 'module' definition found in provided Verilog code.")
        if len(matches) > 1:
            raise ValueError('Multiple modules found. Exactly one is required.')
        return matches[0]

    def _write_temp_verilog(self, verilog_code: str, label: str) -> str:
        """
        Writes the given verilog_code to a temporary .v file in the working_dir.
        Returns the file path.
        """
        import tempfile

        fd, path = tempfile.mkstemp(dir=self.working_dir, prefix=label + '_', suffix='.v')
        with open(fd, 'w') as f:
            f.write(verilog_code)
        return path

    def _run_equiv_method(self, gold_path: str, ref_path: str, gold_top: str, ref_top: str):
        """
        Runs the standard 'equiv -assert' approach.
        Returns (exit_code, stdout, stderr).
        """
        script = f"""
read_verilog {gold_path}
prep -top {gold_top}
rename {gold_top} gold
design -stash gold

read_verilog {ref_path}
prep -top {ref_top}
rename {ref_top} gate
design -stash gate

design -copy-from gold -as gold gold; design -copy-from gate -as gate gate;

# Create an equivalence-check "miter" that instantiates both designs
equiv_make gold gate eq_miter

# Prepare and set eq_miter as the top for the equivalence passes
prep -top eq_miter

# Perform a simple structural equivalence pass
equiv_simple

# Optionally, try an inductive proof to catch certain sequential differences
equiv_induct

# Check equivalence status and assert (fail with non-zero exit if not equivalent)
equiv_status -assert
"""
        return self._run_yosys(script)

    def _run_smt_method(self, gold_path: str, ref_path: str, gold_top: str, ref_top: str):
        """
        Runs a simple SMT-based equivalence check.
        Returns (exit_code, stdout, stderr).

        This example miter approach is minimal and might need enhancement.
        """
        script = f"""
read_verilog {gold_path}
prep -top {gold_top}
rename {gold_top} gold
design -stash gold

read_verilog {ref_path}
prep -top {ref_top}
rename {ref_top} gate
design -stash gate

design -copy-from gold -as gold gold; design -copy-from gate -as gate gate;

miter -equiv -flatten -make_outputs -ignore_gold_x gold gate miter
hierarchy -top miter
write_verilog trace2.v
sat -tempinduct -prove trigger 0 -set-init-undef -enable_undef -set-def-inputs -ignore_unknown_cells -show-ports miter
"""
        return self._run_yosys(script)

    def _analyze_yosys_result(self, code: int, out: str, err: str, method: str) -> Optional[bool]:
        """
        Analyzes the result from Yosys.
        code: process returncode
        out: stdout
        err: stderr
        method: "equiv" or "smt" (for logging only)

        Returns True if proven equivalent, False if proven different,
        or None if unknown / error.
        """
        if code == 0:
            # Typically means success => designs equivalent
            return True

        # code != 0 => either not equivalent or an error
        combined_out = out + '\n' + err
        if 'Assert failed' in combined_out or 'equiv_check' in combined_out:
            # Standard message from 'equiv -assert'
            self.counterexample_info = f'(Method: {method}) A possible counterexample was found.'
            return False

        if 'SAT proof failed' in combined_out or 'SAT proof finished' in combined_out:
            # In some flows, a failing proof means a mismatch
            if 'unsat' in combined_out or 'proved' in combined_out:
                # unsat => assertion is never violated => designs are equivalent
                return True
            else:
                # sat => a violation => mismatch
                self.counterexample_info = f'(Method: {method}) A possible counterexample from SAT-based check.'
                return False

        # If we got here, we do not have a definitive pass/fail
        # We'll store the error for diagnostics
        self.error_message = f'Yosys returned code {code} with output:\n{combined_out}'
        return None

    def _run_yosys(self, script: str):
        """
        Private helper to run Yosys with the given script.
        Returns (exit_code, stdout, stderr).
        """
        import tempfile

        # Create a temp script file
        fd_script, script_path = tempfile.mkstemp(dir=self.working_dir, prefix='run_', suffix='.ys')
        with open(fd_script, 'w') as f:
            f.write(script)

        # Attempt to run Yosys
        try:
            proc = subprocess.run(
                ['yosys', '-c', script_path],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=self.timeout_seconds,
            )
            return proc.returncode, proc.stdout, proc.stderr
        except subprocess.TimeoutExpired as te:
            self.error_message = f'Yosys call timed out after {self.timeout_seconds}s: {te}'
            return 1, '', self.error_message
        except Exception as e:
            self.error_message = f'Yosys execution error: {e}'
            return 1, '', self.error_message
        # finally:
        #     try:
        #         os.remove(script_path)
        #     except OSError:
        #         pass
