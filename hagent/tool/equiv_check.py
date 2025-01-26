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

    But we now call `yosys -p "..."` so the commands are handled by Yosys's command parser
    rather than Tcl mode.
    """

    def __init__(self):
        """
        Initializes the Equiv_check object:
         - yosys_installed: indicates if Yosys is available.
         - error_message: stores any error encountered.
         - equivalence_check_result: last known equivalence outcome (True/False/None).
         - counterexample_info: stores counterexample details if available.
         - timeout_seconds: defaults to 60s for Yosys calls.
         - working_dir: subdirectory to store all temporary files (for .v files, logs).
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
            subprocess.run(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=True
            )
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
          - reference_code: The 'gate' version

        Both must define exactly one module each. If either file defines more or zero modules,
        we raise an exception. We rename the gold top to 'gold', and the gate top to 'gate'.

        Returns:
            True if designs are equivalent,
            False if designs are not equivalent,
            None if unknown (error or timeout).
        """
        if not self.yosys_installed:
            raise RuntimeError("Yosys not installed or setup() not called.")

        # 1) Validate each snippet has exactly one module
        gold_top = self._extract_single_module_name(gold_code)
        ref_top = self._extract_single_module_name(reference_code)

        # 2) Write each design to a temp file
        gold_path = self._write_temp_verilog(gold_code, 'gold')
        ref_path = self._write_temp_verilog(reference_code, 'gate')

        # 3) Run standard 'equiv -assert' approach
        code_equiv, out_equiv, err_equiv = self._run_equiv_method(gold_path, ref_path, gold_top, ref_top)
        method1_result = self._analyze_yosys_result(code_equiv, out_equiv, err_equiv, method='equiv')
        if method1_result is not None:
            self.equivalence_check_result = method1_result
            return method1_result

        # 4) If method 1 inconclusive, do the SMT-based approach
        code_smt, out_smt, err_smt = self._run_smt_method(gold_path, ref_path, gold_top, ref_top)
        method2_result = self._analyze_yosys_result(code_smt, out_smt, err_smt, method='smt')
        self.equivalence_check_result = method2_result
        return method2_result

    def get_error(self) -> str:
        """Returns the error message if any."""
        return self.error_message

    def get_counterexample(self) -> Optional[str]:
        """Returns the stored counterexample info if available."""
        return self.counterexample_info

    # ------------------- Internal Helpers -------------------

    def _extract_single_module_name(self, verilog_code: str) -> str:
        """
        Extract exactly one module name from the verilog_code.
        If there's none or more than one, raise ValueError.
        """
        pattern = r'^\s*module\s+([A-Za-z0-9_]+)\s*(?:\(|;)'
        matches = re.findall(pattern, verilog_code, flags=re.MULTILINE)
        if len(matches) == 0:
            raise ValueError("No 'module' definition found in provided Verilog code.")
        if len(matches) > 1:
            raise ValueError("Multiple modules found. Exactly one is required.")
        return matches[0]

    def _write_temp_verilog(self, verilog_code: str, label: str) -> str:
        """
        Write verilog_code to a temporary .v file in self.working_dir.
        Return the file path.
        """
        import tempfile
        fd, path = tempfile.mkstemp(dir=self.working_dir, prefix=label + '_', suffix='.v')
        with open(fd, 'w') as f:
            f.write(verilog_code)
        return path

    def _run_equiv_method(self, gold_path: str, ref_path: str, gold_top: str, ref_top: str):
        """
        Build a Yosys command string for standard 'equiv -assert' approach,
        then run yoysys with -p.
        """
        cmd = [
            "read_verilog " + gold_path,
            f"prep -top {gold_top}",
            f"rename {gold_top} gold",
            "design -stash gold",

            f"read_verilog {ref_path}",
            f"prep -top {ref_top}",
            f"rename {ref_top} gate",
            "design -stash gate",

            "design -copy-from gold -as gold gold; design -copy-from gate -as gate gate;",

            "# Create an equivalence-check 'miter'",
            "equiv_make gold gate eq_miter",

            "# Prepare eq_miter",
            "prep -top eq_miter",

            "# structural equivalence pass",
            "equiv_simple",

            "# optional inductive check",
            "equiv_induct",

            "# final equivalence status assert (non-zero if mismatch)",
            "equiv_status -assert"
        ]
        full_cmd = "; ".join(cmd)

        return self._run_yosys_command(full_cmd)

    def _run_smt_method(self, gold_path: str, ref_path: str, gold_top: str, ref_top: str):
        """
        Build a Yosys command string for the simple SMT-based approach,
        then run yoysys with -p.
        """
        cmd = [
            f"read_verilog {gold_path}",
            f"prep -top {gold_top}",
            f"rename {gold_top} gold",
            "design -stash gold",

            f"read_verilog {ref_path}",
            f"prep -top {ref_top}",
            f"rename {ref_top} gate",
            "design -stash gate",

            "design -copy-from gold -as gold gold; design -copy-from gate -as gate gate;",

            "miter -equiv -flatten -make_outputs -ignore_gold_x gold gate miter",
            "hierarchy -top miter",
            "write_verilog trace2.v",
            "sat -tempinduct -prove trigger 0 -set-init-undef -enable_undef -set-def-inputs"
            " -ignore_unknown_cells -show-ports miter"
        ]
        full_cmd = "; ".join(cmd)

        return self._run_yosys_command(full_cmd)

    def _run_yosys_command(self, command_str: str):
        """
        Actually call 'yosys -p "command_str"'
        Return (exit_code, stdout, stderr).
        """
        try:
            proc = subprocess.run(
                ["yosys", "-p", command_str],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=self.timeout_seconds
            )
            return proc.returncode, proc.stdout, proc.stderr
        except subprocess.TimeoutExpired as te:
            self.error_message = f"Yosys call timed out after {self.timeout_seconds}s: {te}"
            return 1, "", self.error_message
        except Exception as e:
            self.error_message = f"Yosys execution error: {e}"
            return 1, "", self.error_message

    def _analyze_yosys_result(self, code: int, out: str, err: str, method: str) -> Optional[bool]:
        """
        If code == 0 => success => designs equivalent
        If code != 0 => possible mismatch or unknown
        """
        if code == 0:
            return True

        combined = out + "\n" + err

        # typical mismatch
        if "Assert failed" in combined or "equiv_check" in combined:
            self.counterexample_info = f"(Method: {method}) A possible counterexample was found."
            return False

        # some smt flows
        if "SAT proof failed" in combined or "SAT proof finished" in combined:
            if "unsat" in combined or "proved" in combined:
                return True  # no violation => eq
            else:
                self.counterexample_info = f"(Method: {method}) A possible cex from SAT-based check."
                return False

        # no definitive pass/fail => unknown
        self.error_message = f"Yosys returned code {code} with output:\n{combined}"
        return None
