import os
import re
import subprocess
import tempfile
import sys
from typing import Optional, Tuple, List
from hagent.core.output_manager import get_output_dir
from hagent.tool.file_manager import File_manager


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
         - use_docker: indicates if Docker fallback should be used.
         - file_manager: File_manager instance for Docker operations.
         - error_message: stores any error encountered.
         - equivalence_check_result: last known equivalence outcome (True/False/None).
         - counterexample_info: stores counterexample details if available.
         - timeout_seconds: defaults to 60s for Yosys calls.
        """
        self.yosys_installed = False
        self.use_docker = False
        self.file_manager: Optional[File_manager] = None
        self.error_message = ''
        self.equivalence_check_result: Optional[bool] = None
        self.counterexample_info: Optional[str] = None
        self.timeout_seconds = 120

    def setup(self, yosys_path: Optional[str] = None) -> bool:
        """
        Checks if Yosys is installed, accessible, and meets the minimum version 0.4.
        If yosys_path is provided, that binary is used; otherwise, the system PATH is used.
        If local Yosys is not available, falls back to Docker with mascucsc/hagent-builder:latest.

        Returns True if Yosys is available (locally or via Docker), False otherwise.
        """
        command = [yosys_path, '-V'] if yosys_path else ['yosys', '-V']

        try:
            # Try local Yosys installation first
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
            # Attempt to extract version number (e.g., "0.4" or "0.4.1") from stdout
            match = re.search(r'(\d+\.\d+(?:\.\d+)?)', result.stdout)
            if not match:
                self.yosys_installed = False
                self.error_message = f'Unable to parse Yosys version output: {result.stdout}'
                # Only fall back to Docker if no specific yosys_path was provided
                if yosys_path is None:
                    return self._setup_docker_fallback()
                else:
                    return False

            version_str = match.group(1)
            # Convert version string into a tuple of integers for comparison
            version_tuple = tuple(map(int, version_str.split('.')))
            required_version = (0, 40)

            if version_tuple < required_version:
                self.yosys_installed = False
                self.error_message = f'Yosys version {version_str} is below the required version 0.4'
                # Only fall back to Docker if no specific yosys_path was provided
                if yosys_path is None:
                    return self._setup_docker_fallback()
                else:
                    return False

            self.yosys_installed = True
            self.use_docker = False
            return True

        except (subprocess.CalledProcessError, FileNotFoundError) as e:
            self.yosys_installed = False
            self.error_message = f'Yosys not found or not accessible: {e}'
            # Only fall back to Docker if no specific yosys_path was provided
            if yosys_path is None:
                return self._setup_docker_fallback()
            else:
                return False

    def _setup_docker_fallback(self) -> bool:
        """
        Sets up Docker fallback using File_manager with mascucsc/hagent-builder:latest image.

        Returns True if Docker setup succeeds, False otherwise.
        """
        try:
            self.file_manager = File_manager(image='mascucsc/hagent-builder:latest')
            if self.file_manager.setup():
                # Test that Yosys is available in the Docker container
                rc, out, err = self.file_manager.run('yosys --version')
                if rc == 0 and 'Yosys' in out:
                    self.use_docker = True
                    self.yosys_installed = True
                    return True
                else:
                    self.error_message = f'Yosys not available in Docker container - RC: {rc}, ERR: {err}'
                    return False
            else:
                self.error_message = f'Docker setup failed: {self.file_manager.get_error()}'
                return False
        except Exception as e:
            self.error_message = f'Docker fallback setup error: {e}'
            return False

    def _copy_results_from_docker(self, work_dir: str) -> None:
        """
        Copy any result files from the Docker container back to the local work directory.
        This ensures output files are available in the expected output directory.
        """
        if not self.use_docker or not self.file_manager:
            return

        try:
            # Get patch dictionary to see what files were created in the container
            patches = self.file_manager.get_patch_dict()

            # Copy all new files from the container to the work directory
            if 'full' in patches:
                for file_item in patches['full']:
                    container_path = file_item['filename']
                    # Skip the original input files we copied to the container
                    if container_path.endswith(('.v', '.s')):
                        continue

                    # Get file content and write to local work directory
                    content = self.file_manager.get_file_content(container_path)
                    if content:
                        local_path = os.path.join(work_dir, os.path.basename(container_path))
                        with open(local_path, 'w') as f:
                            f.write(content)

            # Also copy any debug output files that were created in Docker working directory
            debug_files = [
                'equiv_method_stdout.log',
                'equiv_method_stderr.log',
                'equiv_method_output.log',
                'smt_method_stdout.log',
                'smt_method_stderr.log',
                'smt_method_output.log',
            ]

            for debug_file in debug_files:
                try:
                    content = self.file_manager.get_file_content(debug_file)
                    if content:
                        local_path = os.path.join(work_dir, debug_file)
                        with open(local_path, 'w') as f:
                            f.write(content)
                except Exception:
                    # File might not exist if only one method was run, that's okay
                    pass

        except Exception as e:
            # Don't fail the main operation if we can't copy results
            print(f'Warning: Failed to copy results from Docker: {e}', file=sys.stderr)

    def _save_yosys_output(self, work_dir: str, method_name: str, return_code: int, stdout: str, stderr: str) -> None:
        """
        Save Yosys stdout and stderr output to files for debugging.
        For local execution, saves to work_dir. For Docker execution, saves to container working directory.

        Args:
            work_dir: Directory where output files should be saved (local execution only)
            method_name: Name of the method (e.g., 'equiv_method', 'smt_method')
            return_code: Exit code from Yosys command
            stdout: Standard output from Yosys
            stderr: Standard error from Yosys
        """
        try:
            if self.use_docker and self.file_manager:
                # For Docker, save files in the container working directory
                self._save_yosys_output_docker(method_name, return_code, stdout, stderr)
            else:
                # For local execution, save files in the work directory
                self._save_yosys_output_local(work_dir, method_name, return_code, stdout, stderr)

        except Exception as e:
            # Don't fail the main operation if we can't save debug output
            print(f'Warning: Failed to save Yosys output for {method_name}: {e}', file=sys.stderr)

    def _save_yosys_output_local(self, work_dir: str, method_name: str, return_code: int, stdout: str, stderr: str) -> None:
        """Save Yosys output to local files."""
        # Save stdout
        stdout_file = os.path.join(work_dir, f'{method_name}_stdout.log')
        with open(stdout_file, 'w') as f:
            f.write(f'Return code: {return_code}\n')
            f.write(f'Method: {method_name}\n')
            f.write('-' * 50 + '\n')
            f.write(stdout)

        # Save stderr
        stderr_file = os.path.join(work_dir, f'{method_name}_stderr.log')
        with open(stderr_file, 'w') as f:
            f.write(f'Return code: {return_code}\n')
            f.write(f'Method: {method_name}\n')
            f.write('-' * 50 + '\n')
            f.write(stderr)

        # Save combined output with summary
        combined_file = os.path.join(work_dir, f'{method_name}_output.log')
        with open(combined_file, 'w') as f:
            f.write(f'Yosys Equivalence Check - {method_name}\n')
            f.write(f'Return code: {return_code}\n')
            f.write(f'Docker mode: {self.use_docker}\n')
            f.write('=' * 60 + '\n\n')

            f.write('STDOUT:\n')
            f.write('-' * 30 + '\n')
            f.write(stdout)
            f.write('\n\n')

            f.write('STDERR:\n')
            f.write('-' * 30 + '\n')
            f.write(stderr)
            f.write('\n')

    def _save_yosys_output_docker(self, method_name: str, return_code: int, stdout: str, stderr: str) -> None:
        """Save Yosys output to Docker container files."""
        # Create combined output content
        combined_content = f"""Yosys Equivalence Check - {method_name}
Return code: {return_code}
Docker mode: {self.use_docker}
============================================================

STDOUT:
------------------------------
{stdout}

STDERR:
------------------------------
{stderr}
"""

        # Save files in Docker container using file_manager.run()
        files_to_create = [
            (f'{method_name}_stdout.log', f'Return code: {return_code}\nMethod: {method_name}\n{"-" * 50}\n{stdout}'),
            (f'{method_name}_stderr.log', f'Return code: {return_code}\nMethod: {method_name}\n{"-" * 50}\n{stderr}'),
            (f'{method_name}_output.log', combined_content),
        ]

        for filename, content in files_to_create:
            # Use heredoc to write file content in Docker container
            escaped_content = content.replace("'", "'\"'\"'")  # Escape single quotes for heredoc
            cmd = f"cat > {filename} << 'EOF'\n{escaped_content}\nEOF"
            rc, out, err = self.file_manager.run(cmd)
            if rc != 0:
                print(f'Warning: Failed to create {filename} in Docker: {err}', file=sys.stderr)

    def check_equivalence(self, gold_code: str, gate_code: str, desired_top: str = 'SingleCycleCPU') -> Optional[bool]:
        """
        Checks the equivalence of two Verilog designs:
          - gold_code: The 'gold' version to match
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

        # 1) Validate each snippet has exactly one module
        # desired_top = self._extract_single_module_name(gate_code)

        gold_top = self._extract_module_name(gold_code, top_module=desired_top)
        gate_top = self._extract_module_name(gate_code, top_module=desired_top)
        if gold_top == gate_top:
            print(f'gold_top provided = gate_top provided = {gate_top}')
        else:
            raise ValueError(f'Error: gold_top ({gold_top}) and gate_top ({gate_top}) do not match!')

        # 2) Write each design to a temp file
        #
        # Create a subdirectory for working files
        work_dir = tempfile.mkdtemp(dir=get_output_dir(), prefix='equiv_check_')

        if self.use_docker:
            # For Docker, we need to setup file tracking and copy files to container
            self.file_manager.track_dir('.')

            # Write files locally first, then copy to container
            gold_v_filename = self._write_temp_verilog(work_dir, gold_code, 'gold')
            gate_v_filename = self._write_temp_verilog(work_dir, gate_code, 'gate')

            # Copy files to container
            gold_container_path = 'gold.v'
            gate_container_path = 'gate.v'

            if not self.file_manager.copy_file(gold_v_filename, gold_container_path):
                raise RuntimeError(f'Failed to copy gold file to container: {self.file_manager.get_error()}')
            if not self.file_manager.copy_file(gate_v_filename, gate_container_path):
                raise RuntimeError(f'Failed to copy gate file to container: {self.file_manager.get_error()}')

            # Use container paths for processing
            gold_v_filename = gold_container_path
            gate_v_filename = gate_container_path
        else:
            # Local execution - write files directly
            gold_v_filename = self._write_temp_verilog(work_dir, gold_code, 'gold')
            gate_v_filename = self._write_temp_verilog(work_dir, gate_code, 'gate')

        # 3) Run standard 'equiv -assert' approach
        code_equiv, out_equiv, err_equiv = self._run_equiv_method(work_dir, gold_v_filename, gate_v_filename, gold_top, gate_top)

        # Save method 1 output for debugging
        self._save_yosys_output(work_dir, 'equiv_method', code_equiv, out_equiv, err_equiv)

        method1_result = self._analyze_yosys_result(code_equiv, out_equiv, err_equiv, method='equiv')

        # Initialize variables for method 2 (might not be used)
        method2_result = None

        if method1_result is not None:
            self.equivalence_check_result = method1_result
            if method1_result is False:
                # store parsed failures into counterexample_info
                failures = self.parse_equiv_failures(out_equiv, err_equiv)
                if failures:
                    self.counterexample_info = failures
            final_result = method1_result
        else:
            # 4) If method 1 inconclusive, do the SMT-based approach
            code_smt, out_smt, err_smt = self._run_smt_method(work_dir, gold_v_filename, gate_v_filename, gold_top, gate_top)

            # Save method 2 output for debugging
            self._save_yosys_output(work_dir, 'smt_method', code_smt, out_smt, err_smt)

            method2_result = self._analyze_yosys_result(code_smt, out_smt, err_smt, method='smt')
            self.equivalence_check_result = method2_result
            final_result = method2_result

        # 5) Copy results back to output directory if using Docker
        if self.use_docker:
            self._copy_results_from_docker(work_dir)

        return final_result

    def get_error(self) -> str:
        """Returns the error message if any."""
        return self.error_message

    def get_counterexample(self) -> Optional[str]:
        """Returns the stored counterexample info if available."""
        return self.counterexample_info

    def parse_equiv_failures(self, out: str, err: str) -> List[Tuple[str, str]]:
        """
        Scan Yosys stdout/stderr for lines indicating an unproven $equiv. Return
        a list of (module_name, io_name) pairs, or, if we only see the summary
        "Found N unproven $equiv cells", return a placeholder entry
        ("<summary>", "<N unproven equiv cells>").
        """
        failures: List[Tuple[str, str]] = []

        # Pattern 1: “Trying to prove $equiv for \MODULE.IO: failed.”
        pat1 = re.compile(r"""Trying to prove \$equiv for \\([A-Za-z0-9_]+)\.([A-Za-z0-9_]+):\s*failed""")

        # Pattern 2: “Unproven $equiv ...: \MODULE.IO_NAME_gold \MODULE.IO_NAME_gate”
        pat2 = re.compile(r"""Unproven \$equiv [^:]*:\s*\\([A-Za-z0-9_]+)\.([A-Za-z0-9_]+)_(?:gold|gate)""")

        # Pattern 3: summary "ERROR: Found N unproven $equiv cells in 'equiv_status ...'."
        pat3 = re.compile(r"""ERROR:\s*Found\s+(\d+)\s+unproven\s+\$equiv\s+cells""", flags=re.IGNORECASE)

        for line in out.splitlines() + err.splitlines():
            # Check for "Trying to prove $equiv for \Module.IO: failed"
            m1 = pat1.search(line)
            if m1:
                module, io_name = m1.group(1), m1.group(2)
                failures.append((module, io_name))
                continue

            # Check for "Unproven $equiv ...: \Module.IO_gold \Module.IO_gate"
            m2 = pat2.search(line)
            if m2:
                module, io_name = m2.group(1), m2.group(2)
                failures.append((module, io_name))
                continue

            # Check for summary "ERROR: Found 3 unproven $equiv cells"
            m3 = pat3.search(line)
            if m3:
                count = m3.group(1)
                # We don't know module/IO here, just store a summary
                failures.append(('<summary>', f'{count} unproven $equiv cells'))
                continue

        return failures

    # ------------------- Internal Helpers -------------------

    # def _extract_single_module_name(self, verilog_code: str) -> str:
    #     """
    #     Extract exactly one module name from the verilog_code.
    #     If there's none or more than one, raise ValueError.
    #     """
    #     pattern = r'^\s*module\s+([A-Za-z0-9_]+)\s*(?:\(|;)'
    #     matches = re.findall(pattern, verilog_code, flags=re.MULTILINE)
    #     if len(matches) == 0:
    #         raise ValueError("No 'module' definition found in provided Verilog code.")
    #     if len(matches) > 1:
    #         raise ValueError('Multiple modules found. Exactly one is required.')
    #     return matches[0]
    def _extract_module_name(self, verilog_code: str, top_module: Optional[str] = None) -> str:
        """
        Extract a module name from the verilog_code.
        If top_module is specified and found, return it.
        Otherwise, if there's exactly one module, return it.
        If there's none or more than one without a specified top module, raise ValueError.
        """
        pattern = r'^\s*module\s+([A-Za-z0-9_]+)\s*(?:\(|;)'
        matches = re.findall(pattern, verilog_code, flags=re.MULTILINE)
        if top_module:
            if top_module in matches:
                return top_module
            else:
                raise ValueError(f"Specified top module '{top_module}' not found in the provided Verilog code.")
        if len(matches) == 0:
            raise ValueError("No 'module' definition found in provided Verilog code.")
        if len(matches) > 1:
            raise ValueError('Multiple modules found. Exactly one is required unless a top module is specified.')
        return matches[0]

    def _write_temp_verilog(self, work_dir: str, verilog_code: str, label: str) -> str:
        """
        Write verilog_code to a temporary .v file in temporary directory.
        Return the file path.
        """

        filename = os.path.join(work_dir, f'{label}.v')
        with open(filename, 'w') as f:
            f.write(verilog_code)
        return filename

    def _run_equiv_method(
        self, work_dir: str, gold_v_filename: str, gate_v_filename: str, gold_top: str, gate_top: str
    ) -> Tuple[int, str, str]:
        """
        Build a Yosys command string for standard 'equiv -assert' approach
        """
        cmd = [
            f'read_verilog -sv {gold_v_filename}',
            f'prep -flatten -top {gold_top}',
            f'rename {gold_top} gold',
            'design -stash gold',
            f'read_verilog -sv {gate_v_filename}',
            f'prep -flatten -top {gate_top}',
            f'rename {gate_top} gate',
            'design -stash gate',
            'design -copy-from gold -as gold gold; design -copy-from gate -as gate gate',
            "# Create an equivalence-check 'miter'",
            'equiv_make gold gate eq_miter',
            '# Prepare eq_miter',
            'prep -flatten -top eq_miter',
            '# structural equivalence pass',
            'equiv_simple -undef -seq 2',
            '# optional inductive check',
            'equiv_induct -undef',
            '# final equivalence status assert (non-zero if mismatch)',
            'equiv_status -assert',
        ]
        full_cmd = ';\n'.join(cmd)

        if self.use_docker:
            # For Docker, create script in container working directory
            script_name = 'check1.s'
            rc, _, _ = self.file_manager.run(f"cat > {script_name} << 'EOF'\n{full_cmd}\nEOF")
            if rc != 0:
                return rc, '', 'Failed to create script in container'
            return self._run_yosys_command(script_name)
        else:
            # For local execution, create script file locally
            filename = os.path.join(work_dir, 'check1.s')
            with open(filename, 'w') as f:
                f.write(full_cmd)
            return self._run_yosys_command(filename)

    def _run_smt_method(
        self, work_dir: str, gold_v_filename: str, gate_v_filename: str, gold_top: str, gate_top: str
    ) -> Tuple[int, str, str]:
        """
        Build a Yosys command string for the simple SMT-based approach,
        """
        cmd = [
            f'read_verilog {gold_v_filename}',
            f'prep -top {gold_top}',
            f'rename {gold_top} gold',
            'design -stash gold',
            f'read_verilog {gate_v_filename}',
            f'prep -top {gate_top}',
            f'rename {gate_top} gate',
            'design -stash gate',
            'design -copy-from gold -as gold gold; design -copy-from gate -as gate gate;',
            'miter -equiv -flatten -make_outputs -ignore_gold_x gold gate miter',
            'hierarchy -top miter',
            'sat -tempinduct -prove trigger 0 -set-init-undef -enable_undef -set-def-inputs'
            ' -ignore_unknown_cells -show-ports miter',
        ]
        full_cmd = ';\n'.join(cmd)

        if self.use_docker:
            # For Docker, create script in container working directory
            script_name = 'check2.s'
            rc, _, _ = self.file_manager.run(f"cat > {script_name} << 'EOF'\n{full_cmd}\nEOF")
            if rc != 0:
                return rc, '', 'Failed to create script in container'
            return self._run_yosys_command(script_name)
        else:
            # For local execution, create script file locally
            filename = os.path.join(work_dir, 'check2.s')
            with open(filename, 'w') as f:
                f.write(full_cmd)
            return self._run_yosys_command(filename)

    def _run_yosys_command(self, filename: str) -> Tuple[int, str, str]:
        """
        Actually call 'yosys -s filename' either locally or via Docker.
        Return (exit_code, stdout, stderr).
        """
        if self.use_docker and self.file_manager:
            # Docker execution
            try:
                # For Docker, filename should be just the script name (not full path)
                script_name = os.path.basename(filename)

                # Copy script to container if it's a local path
                if os.path.exists(filename):
                    if not self.file_manager.copy_file(filename, script_name):
                        self.error_message = f'Failed to copy script to container: {self.file_manager.get_error()}'
                        return 1, '', self.error_message

                rc, stdout, stderr = self.file_manager.run(f'yosys -s {script_name}')
                return rc, stdout, stderr
            except Exception as e:
                self.error_message = f'Docker Yosys execution error: {e}'
                return 1, '', self.error_message
        else:
            # Local execution
            try:
                proc = subprocess.run(
                    ['yosys', '-s', filename],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    timeout=self.timeout_seconds,
                )
                return proc.returncode, proc.stdout, proc.stderr
            except subprocess.TimeoutExpired as te:
                self.error_message = f'Yosys call timeout after {self.timeout_seconds}s: {te}'
                return 1, '', self.error_message
            except Exception as e:
                self.error_message = f'Yosys execution error: {e}'
                return 1, '', self.error_message

    def _analyze_yosys_result(self, code: int, out: str, err: str, method: str) -> Optional[bool]:
        if 'ERROR' in err:
            print('WARNING: YOSYS failed to check with this message (likely a Verilog Syntax Error)', file=sys.stderr)
            print(err, file=sys.stderr)
            return False

        if 'timeout' in err:
            return None

        if method == 'smt':
            pattern = re.compile(r'^SAT.*FAIL.*$', flags=re.MULTILINE)
            # Find all matching lines
            matching_lines = pattern.findall(out)
            return len(matching_lines) == 0
        elif method == 'equiv':
            return code == 0

        # no definitive pass/fail => unknown
        self.error_message = f'Yosys returned code {code} with error:\n{err}'
        return None
