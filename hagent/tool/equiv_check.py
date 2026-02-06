import os
import re
import subprocess
import tempfile
import sys
from pathlib import Path
from typing import Optional, Tuple, List
from hagent.inou.path_manager import PathManager
from hagent.inou.runner import Runner
from hagent.tool.compile_slang import Compile_slang


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
         - runner: Runner instance for unified operations.
         - error_message: stores any error encountered.
         - equivalence_check_result: last known equivalence outcome (True/False/None).
         - counterexample_info: stores counterexample details if available.
         - timeout_seconds: defaults to 60s for Yosys calls.
        """
        self.yosys_installed = False
        self.use_docker = False
        self.runner: Optional[Runner] = None
        self.error_message = ''
        self.equivalence_check_result: Optional[bool] = None
        self.counterexample_info: Optional[str] = None
        self.timeout_seconds = 120

    def setup(self, try_local: bool = True) -> bool:
        """
        Checks if Yosys is installed, accessible, and meets the minimum version 0.4.
        If local Yosys is not available, falls back to Docker with mascucsc/hagent-simplechisel:2026.02.

        Returns True if Yosys is available (locally or via Docker), False otherwise.
        """

        if not try_local:
            return self._setup_docker_fallback()

        command = ['yosys', '-V']

        try:
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
            match = re.search(r'(\d+\.\d+(?:\.\d+)?)', result.stdout)
            if not match:
                self.yosys_installed = False
                self.error_message = f'Unable to parse Yosys version output: {result.stdout}'
                original_error = self.error_message
                if self._setup_docker_fallback():
                    return True
                self.error_message = original_error
                return False

            version_tuple = tuple(map(int, match.group(1).split('.')))
            required_version = (0, 40)
            if version_tuple < required_version:
                self.yosys_installed = False
                self.error_message = f'Yosys version {".".join(map(str, version_tuple))} is below the required version 0.4'
                original_error = self.error_message
                if self._setup_docker_fallback():
                    return True
                self.error_message = original_error
                return False

            self.yosys_installed = True
            self.use_docker = False
            return True

        except (subprocess.CalledProcessError, FileNotFoundError) as e:
            self.yosys_installed = False
            self.error_message = f'Yosys not found or not accessible: {e}'
            return self._setup_docker_fallback()

    def _setup_docker_fallback(self) -> bool:
        """
        Sets up Docker fallback using ContainerManager with mascucsc/hagent-simplechisel:2026.02 image.
        Uses no mount points - files are copied in/out as needed.

        Returns True if Docker setup succeeds, False otherwise.
        """

        docker_image = 'mascucsc/hagent-simplechisel:2026.02'
        try:
            self.runner = Runner(docker_image=docker_image)
            if not self.runner.setup():
                self.error_message = f'Docker setup failed: {self.runner.get_error()}'
                return False

            rc, out, err = self.runner.run_cmd('yosys --version')
            if rc == 0 and 'Yosys' in out:
                self.use_docker = True
                self.yosys_installed = True
                return True

            self.error_message = f'Yosys not available in Docker container - RC: {rc}, ERR: {err}'
            return False
        except Exception as e:
            self.error_message = f'Docker fallback setup error: {e}'
            return False

    def _translate_to_container(self, host_path: str) -> str:
        """
        Translate a host path to container path when running in Docker mode.
        Falls back to the original path in local mode.
        """
        if not self.runner or not self.runner.is_docker_mode():
            return host_path

        path_manager = PathManager()
        host_path_obj = Path(host_path).resolve()

        # Define container roots explicitly (workspace layout)
        container_roots = {
            'repo': Path('/code/workspace/repo'),
            'build': Path('/code/workspace/build'),
            'cache': Path('/code/workspace/cache'),
            'tech': Path('/code/workspace/tech'),
            'private': Path('/code/workspace/private'),
        }

        mappings = [
            (path_manager.repo_mount_dir or path_manager.repo_dir, container_roots['repo']),
            (path_manager.build_mount_dir or path_manager.build_dir, container_roots['build']),
            (path_manager.cache_mount_dir or path_manager.cache_dir, container_roots['cache']),
            (path_manager.tech_mount_dir or path_manager.tech_dir, container_roots['tech']),
            (
                path_manager.private_mount_dir or path_manager.private_dir,
                container_roots['private'] if path_manager.private_dir else None,
            ),
        ]

        for local_root, container_root in mappings:
            if not local_root or container_root is None:
                continue
            try:
                if host_path_obj == local_root or local_root in host_path_obj.parents:
                    relative = host_path_obj.relative_to(local_root)
                    return str(container_root / relative)
            except ValueError:
                continue

        # Fallback: place it under cache in the container
        return str(container_roots['cache'] / host_path_obj.name)

    def _write_text(self, path: str, content: str) -> bool:
        """Write text using Runner filesystem when available."""
        if self.runner and self.runner.filesystem:
            return self.runner.filesystem.write_text(path, content)
        try:
            with open(path, 'w') as f:
                f.write(content)
            return True
        except Exception as exc:
            self.error_message = str(exc)
            return False

    def _copy_results_from_docker(self, work_dir: str) -> None:
        """
        Copy any result files from the Docker container back to the local work directory.
        This ensures output files are available in the expected output directory.
        """
        if not self.use_docker or not self.runner:
            return

        try:
            container_work_dir = self._translate_to_container(work_dir)

            # Get list of files to copy from the container work directory
            # We want to copy check.s script and any .log files
            rc, out, err = self.runner.run_cmd(
                f'find {container_work_dir} -type f \\( -name "check.s" -o -name "*.log" \\) 2>/dev/null || true'
            )
            if rc != 0:
                print(f'Warning: Failed to list files in Docker work directory {container_work_dir}: {err}', file=sys.stderr)
                return

            files_to_copy = []
            for line in out.strip().split('\n'):
                if line.strip():
                    files_to_copy.append(line.strip())

            # Copy each file from container to local work directory using filesystem
            for container_file_path in files_to_copy:
                local_file_path = os.path.join(work_dir, os.path.basename(container_file_path))

                # Use filesystem to read and write files
                try:
                    if self.runner.filesystem:
                        file_content = self.runner.filesystem.read_text(container_file_path)
                        # Write to local file using standard Python (since this is for local output)
                        with open(local_file_path, 'w') as f:
                            f.write(file_content)
                    else:
                        # Fallback to run_cmd if filesystem not available
                        rc, file_content, err = self.runner.run_cmd(f'cat {container_file_path}')
                        if rc == 0:
                            with open(local_file_path, 'w') as f:
                                f.write(file_content)
                        else:
                            print(f'Warning: Failed to read {container_file_path} from Docker: {err}', file=sys.stderr)
                except Exception as read_err:
                    print(f'Warning: Failed to read {container_file_path} from Docker: {read_err}', file=sys.stderr)

        except Exception as e:
            # Don't fail the main operation if we can't copy results
            print(f'Warning: Failed to copy results from Docker: {e}', file=sys.stderr)

    def _save_yosys_output(self, work_dir: str, method_name: str, return_code: int, stdout: str, stderr: str) -> None:
        """
        Save Yosys stdout and stderr output to files for debugging.
        For local execution, saves to work_dir. For Docker execution, saves to container working directory.

        Args:
            work_dir: Directory where output files should be saved
            method_name: Name of the method (e.g., 'equiv_method', 'smt_method')
            return_code: Exit code from Yosys command
            stdout: Standard output from Yosys
            stderr: Standard error from Yosys
        """
        try:
            # Save Yosys output using unified approach
            if self.runner and self.runner.filesystem:
                # Use unified FileSystem approach
                self._save_yosys_output_unified(work_dir, method_name, return_code, stdout, stderr)
            elif self.use_docker and self.runner:
                # Fallback to Docker-specific method
                self._save_yosys_output_docker(work_dir, method_name, return_code, stdout, stderr)
            else:
                # Fallback to local method
                self._save_yosys_output_local(work_dir, method_name, return_code, stdout, stderr)

        except Exception as e:
            # Don't fail the main operation if we can't save debug output
            print(f'Warning: Failed to save Yosys output for {method_name}: {e}', file=sys.stderr)

    def _save_yosys_output_unified(self, work_dir: str, method_name: str, return_code: int, stdout: str, stderr: str) -> None:
        """Save Yosys output using unified FileSystem approach."""
        filesystem = self.runner.filesystem

        # Create output files using FileSystem
        stdout_content = f'Return code: {return_code}\nMethod: {method_name}\n{"-" * 50}\n{stdout}'
        stderr_content = f'Return code: {return_code}\nMethod: {method_name}\n{"-" * 50}\n{stderr}'

        import os

        stdout_file = os.path.join(work_dir, f'{method_name}_stdout.log')
        stderr_file = os.path.join(work_dir, f'{method_name}_stderr.log')

        # Write using unified FileSystem - works in both local and Docker!
        filesystem.write_text(stdout_file, stdout_content)
        filesystem.write_text(stderr_file, stderr_content)

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

    def _save_yosys_output_docker(self, work_dir: str, method_name: str, return_code: int, stdout: str, stderr: str) -> None:
        """Save Yosys output to Docker container files."""
        container_work_dir = self._translate_to_container(work_dir)

        stdout_content = 'Return code: {}\nMethod: {}\n{}\n{}'.format(return_code, method_name, '-' * 50, stdout)
        stderr_content = 'Return code: {}\nMethod: {}\n{}\n{}'.format(return_code, method_name, '-' * 50, stderr)

        files_to_create = [
            (f'{container_work_dir}/{method_name}_stdout.log', stdout_content),
            (f'{container_work_dir}/{method_name}_stderr.log', stderr_content),
        ]

        for filename, content in files_to_create:
            if not self._write_text(filename, content):
                print(f'Warning: Failed to create {filename} in Docker: {self.error_message}', file=sys.stderr)

    def check_equivalence(self, gold_code: str, gate_code: str, desired_top: str = '') -> Optional[bool]:
        """
        Checks the equivalence of two Verilog designs:
          - gold_code: The 'gold' version to match
          - gate_code: The 'gate' version
          - desired_top: Optional top module name for gold design

        If desired_top is provided, it's used for the gold design, and we find the matching
        module in gate_code based on IO compatibility. If no desired_top is provided,
        we match top modules based on IO compatibility.

        Returns:
            True if designs are equivalent,
            False if designs are not equivalent,
            None if unknown (error or timeout).
        """
        if not self.yosys_installed:
            raise RuntimeError('Yosys not installed or setup() not called.')

        # Find matching top modules
        module_pairs = self._find_matching_tops(gold_code, gate_code, desired_top)

        # DEBUG: Show what modules were actually found in each design
        print('🔍 [DEBUG] Module pairs found for comparison:')
        for i, (gold_top, gate_top) in enumerate(module_pairs):
            print(f'     Pair {i + 1}: {gold_top} (golden) ↔ {gate_top} (gate)')
        if not module_pairs:
            print('     ❌ No module pairs found!')
        else:
            print(f'     Total pairs to check: {len(module_pairs)}')

        # 2) Write each design to a temp file
        #
        # Create a subdirectory for working files
        work_dir = tempfile.mkdtemp(dir=PathManager().get_cache_dir(), prefix='equiv_check_')

        # Ensure container working directory exists when running in Docker mode
        if self.use_docker and self.runner:
            container_work_dir = self._translate_to_container(work_dir)
            try:
                if self.runner.filesystem:
                    self.runner.filesystem.makedirs(container_work_dir, exist_ok=True)
                else:
                    # Best-effort fallback
                    self.runner.run_cmd(f'mkdir -p {container_work_dir}', quiet=True)
            except Exception:
                pass

        # Track working directory for file changes (works in both local and Docker modes)
        if self.runner:
            tracked_dir = self._translate_to_container(work_dir) if self.use_docker else work_dir
            self.runner.track_dir(tracked_dir)

        gold_v_filename = self._write_temp_verilog(work_dir, gold_code, 'gold')
        gate_v_filename = self._write_temp_verilog(work_dir, gate_code, 'gate')

        # 3) Run SMT-based approach for each module pair
        all_results = []
        all_counterexamples = []

        for i, (gold_top, gate_top) in enumerate(module_pairs):
            print(f'Checking equivalence: {gold_top} ↔ {gate_top}')

            code_smt, out_smt, err_smt = self._run_smt_method(work_dir, gold_v_filename, gate_v_filename, gold_top, gate_top)

            # Save method output for debugging
            self._save_yosys_output(work_dir, f'smt_method_{i}', code_smt, out_smt, err_smt)

            result = self._analyze_yosys_result(code_smt, out_smt, err_smt, method='smt')
            all_results.append((gold_top, gate_top, result))

            if result is False:
                # store parsed failures for this pair
                failures = self._parse_equiv_failures(out_smt, err_smt)
                signal_table = self._parse_signal_table(out_smt, err_smt)
                if signal_table:
                    all_counterexamples.append(f'Module pair {gold_top}↔{gate_top}:\n{signal_table}')
                elif failures:
                    all_counterexamples.append(f'Module pair {gold_top}↔{gate_top}: {str(failures)}')

        # Determine overall result: True if all pairs are equivalent, False if any are not, None if any are inconclusive
        overall_result = True
        for gold_top, gate_top, result in all_results:
            if result is False:
                overall_result = False
                break
            elif result is None:
                overall_result = None  # Inconclusive if any pair is inconclusive

        self.equivalence_check_result = overall_result

        # Combine counterexamples
        if all_counterexamples:
            self.counterexample_info = '\n\n'.join(all_counterexamples)
        else:
            self.counterexample_info = None

        # 5) Copy results back to output directory if using Docker
        if self.use_docker:
            self._copy_results_from_docker(work_dir)

        return overall_result

    def get_error(self) -> str:
        """Returns the error message if any."""
        return self.error_message

    def get_counterexample(self) -> Optional[str]:
        """Returns the stored counterexample info if available."""
        return self.counterexample_info

    def _parse_equiv_failures(self, out: str, err: str) -> List[Tuple[str, str]]:
        """
        Scan Yosys stdout/stderr for lines indicating an unproven $equiv. Return
        a list of (module_name, io_name) pairs, or, if we only see the summary
        "Found N unproven $equiv cells", return a placeholder entry
        ("<summary>", "<N unproven equiv cells>").
        """
        failures: List[Tuple[str, str]] = []

        # Pattern 1: “Trying to prove $equiv for \MODULE.IO: failed.”
        pat1 = re.compile(r'Trying to prove \$equiv for \\([A-Za-z0-9_]+)\.([A-Za-z0-9_]+):\s*failed')

        # Pattern 2: “Unproven $equiv ...: \MODULE.IO_NAME_gold \MODULE.IO_NAME_gate”
        pat2 = re.compile(r'Unproven \$equiv [^:]*:\s*\\([A-Za-z0-9_]+)\.([A-Za-z0-9_]+)_(?:gold|gate)')

        # Pattern 3: summary "ERROR: Found N unproven $equiv cells in 'equiv_status ...'."
        pat3 = re.compile(r'ERROR:\s*Found\s+(\d+)\s+unproven\s+\$equiv\s+cells', flags=re.IGNORECASE)

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

    def _parse_signal_table(self, out: str, err: str) -> Optional[str]:
        """
        Extract the signal table from Yosys output when a counterexample is found.
        Returns the signal table as a formatted string if found, None otherwise.
        """
        combined_output = out + '\n' + err

        # Look for the signal table header pattern
        lines = combined_output.split('\n')
        table_start = -1

        # Find the start of the signal table
        for i, line in enumerate(lines):
            if 'Signal' in line and 'Dec' in line and 'Hex' in line and 'Bin' in line:
                table_start = i
                break

        if table_start == -1:
            return None

        # Extract the table header and data lines
        table_lines = []
        table_lines.append(lines[table_start])  # Header line

        # Find the separator line (dashes)
        separator_found = False
        for i in range(table_start + 1, len(lines)):
            line = lines[i].strip()
            if line and '----' in line:
                table_lines.append(lines[i])
                separator_found = True
                continue
            elif separator_found and line:
                # This should be a data line
                if line.startswith((' ', '\t')) or any(c.isdigit() for c in line):
                    table_lines.append(lines[i])
                else:
                    # End of table
                    break
            elif separator_found:
                # Empty line might end the table
                break

        if len(table_lines) <= 2:  # Just header and separator
            return None

        return '\n'.join(table_lines)

    def _find_matching_tops(self, gold_code: str, gate_code: str, desired_top: str = '') -> List[Tuple[str, str]]:
        """
        Find matching top modules between gold and gate designs.

        Args:
            gold_code: Gold Verilog code
            gate_code: Gate Verilog code
            desired_top: Optional desired top module name for gold

        Returns:
            List of tuples (gold_top_name, gate_top_name) for each matched pair

        Raises:
            ValueError: If no matching modules found or IO mismatch
        """
        # Use slang to analyze both designs
        gold_slang = Compile_slang()
        gate_slang = Compile_slang()

        if not gold_slang.setup() or not gate_slang.setup():
            # Fall back to regex if slang not available
            return self._fallback_module_matching(gold_code, gate_code, desired_top)

        # Add code to slang compilers
        if not gold_slang.add_inline(gold_code) or not gate_slang.add_inline(gate_code):
            # Fall back to regex if slang fails
            return self._fallback_module_matching(gold_code, gate_code, desired_top)

        # Get top module lists
        gold_tops = gold_slang.get_top_list()
        gate_tops = gate_slang.get_top_list()

        if not gold_tops or not gate_tops:
            # Fall back to regex if no tops found
            return self._fallback_module_matching(gold_code, gate_code, desired_top)

        # Case 1: desired_top provided - use it for gold and find matching gate
        if desired_top:
            if desired_top not in gold_tops:
                raise ValueError(f"Specified top module '{desired_top}' not found in gold design. Available: {gold_tops}")

            gold_top = desired_top
            gold_ios = gold_slang.get_ios(gold_top)

            # Find gate module with matching IOs
            matching_gate_top = None
            for gate_top_candidate in gate_tops:
                gate_ios = gate_slang.get_ios(gate_top_candidate)
                if self._ios_match(gold_ios, gate_ios):
                    matching_gate_top = gate_top_candidate
                    break

            if not matching_gate_top:
                raise ValueError(
                    f"No gate module found with IOs matching gold module '{gold_top}'. Gold IOs: {self._format_ios(gold_ios)}"
                )

            return [(gold_top, matching_gate_top)]

        # Case 2: No desired_top - match all gold top modules with compatible gate modules
        matched_pairs = []
        unmatched_gold_modules = []

        for gold_top_candidate in gold_tops:
            gold_ios = gold_slang.get_ios(gold_top_candidate)

            # Find a matching gate module for this gold module
            matching_gate_top = None
            for gate_top_candidate in gate_tops:
                gate_ios = gate_slang.get_ios(gate_top_candidate)
                if self._ios_match(gold_ios, gate_ios):
                    matching_gate_top = gate_top_candidate
                    break

            if matching_gate_top:
                matched_pairs.append((gold_top_candidate, matching_gate_top))
            else:
                unmatched_gold_modules.append((gold_top_candidate, self._format_ios(gold_ios)))

        # Check if all gold modules found matches
        if unmatched_gold_modules:
            unmatched_info = [f'{name}: {ios}' for name, ios in unmatched_gold_modules]
            gate_info = [(top, self._format_ios(gate_slang.get_ios(top))) for top in gate_tops]
            raise ValueError(
                f'Some gold modules could not find matching gate modules.\n'
                f'Unmatched gold modules: {unmatched_info}\n'
                f'Available gate modules: {gate_info}'
            )

        if not matched_pairs:
            raise ValueError('No top modules found for equivalence checking')

        return matched_pairs

    def _fallback_module_matching(self, gold_code: str, gate_code: str, desired_top: str) -> List[Tuple[str, str]]:
        """Fallback to regex-based module matching when slang is not available"""
        if desired_top:
            gold_top = self._extract_module_name(gold_code, top_module=desired_top)
            # Try to find the same module name in gate_code, if not found, use any single module
            try:
                gate_top = self._extract_module_name(gate_code, top_module=desired_top)
            except ValueError:
                # Module name not found in gate, try to get any single module
                gate_top = self._extract_module_name(gate_code)
        else:
            gold_top = self._extract_module_name(gold_code)
            gate_top = self._extract_module_name(gate_code)

        return [(gold_top, gate_top)]

    def _ios_match(self, ios1: List, ios2: List) -> bool:
        """
        Check if two IO lists are compatible (same ports, directions, and bit widths).

        Args:
            ios1: List of IO objects from first module
            ios2: List of IO objects from second module

        Returns:
            True if IOs match, False otherwise
        """
        if len(ios1) != len(ios2):
            return False

        # Sort both lists by name for comparison
        sorted_ios1 = sorted(ios1, key=lambda x: x.name)
        sorted_ios2 = sorted(ios2, key=lambda x: x.name)

        for io1, io2 in zip(sorted_ios1, sorted_ios2):
            if io1.name != io2.name or io1.input != io2.input or io1.output != io2.output or io1.bits != io2.bits:
                return False

        return True

    def _format_ios(self, ios: List) -> str:
        """Format IO list for user-friendly display"""
        if not ios:
            return 'no IOs'
        io_strs = []
        for io in ios:
            direction = 'input' if io.input else 'output' if io.output else 'inout'
            io_strs.append(f'{io.name}({direction}, {io.bits}b)')
        return ', '.join(io_strs)

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
        Write verilog_code to a temporary .v file using Builder's filesystem.
        Return the file path.
        """
        filename = os.path.join(work_dir, f'{label}.v')

        # Print file info for debugging
        lines = verilog_code.split('\n')
        print(f'📁 [LEC] Writing {label}.v file: {filename}')
        print(f'     📊 File size: {len(verilog_code)} chars, {len(lines)} lines')
        print('     🔍 First 3 lines:')
        for i, line in enumerate(lines[:3]):
            print(f'         {i + 1}: {line}')
        if len(lines) > 3:
            print(f'     ... ({len(lines) - 3} more lines)')

        if self.use_docker and self.runner:
            container_work_dir = self._translate_to_container(work_dir)
            container_filename = f'{container_work_dir}/{label}.v'
            # Ensure the directory exists inside the container
            if self.runner.filesystem:
                self.runner.filesystem.makedirs(container_work_dir, exist_ok=True)
            if not self._write_text(container_filename, verilog_code):
                raise RuntimeError(f'Failed to create {label}.v in container: {self.error_message}')
            # In Docker mode, return container path - local write would fail due to permission issues
            return container_filename
        else:
            # Only write locally in local mode
            with open(filename, 'w') as f:
                f.write(verilog_code)
            return filename

    def _run_smt_method(
        self,
        work_dir: str,
        gold_v_filename: str,
        gate_v_filename: str,
        gold_top: str,
        gate_top: str,
    ) -> Tuple[int, str, str]:
        """
        Build a Yosys command string for the simple SMT-based approach,
        """
        cmd = [
            f'read_verilog -sv {gold_v_filename}',
            f'prep -top {gold_top}',
            f'rename {gold_top} gold',
            'design -stash gold',
            f'read_verilog -sv {gate_v_filename}',
            f'prep -top {gate_top}',
            f'rename {gate_top} gate',
            'design -stash gate',
            'design -copy-from gold -as gold gold; design -copy-from gate -as gate gate;',
            'miter -equiv -flatten -make_outputs -ignore_gold_x gold gate miter',
            'hierarchy -top miter',
            'sat -tempinduct -prove trigger 0 -set-init-undef -enable_undef -set-def-inputs -ignore_unknown_cells -show-ports miter',
        ]
        full_cmd = ';\n'.join(cmd)

        if self.use_docker:
            if not self.runner:
                return 1, '', 'Docker mode enabled but Runner is not initialized'
            container_work_dir = self._translate_to_container(work_dir)

            script_name = 'check.s'
            container_script_path = f'{container_work_dir}/{script_name}'

            # Use relative paths in the script since we run from container_work_dir
            relative_gold = os.path.basename(gold_v_filename)
            relative_gate = os.path.basename(gate_v_filename)
            cmd[0] = f'read_verilog -sv {relative_gold}'
            cmd[4] = f'read_verilog -sv {relative_gate}'
            full_cmd = ';\n'.join(cmd) + '\n'

            # Create the script using filesystem or fallback to write_text
            if self.runner.filesystem:
                if not self.runner.filesystem.write_text(container_script_path, full_cmd):
                    return 1, '', 'Failed to create script in container using filesystem'
            else:
                if not self._write_text(container_script_path, full_cmd):
                    return 1, '', f'Failed to create script in container: {self.error_message}'

            # Run Yosys from within container_work_dir
            yosys_cmd = f'cd {container_work_dir} && yosys -s {script_name}'
            return self._run_yosys_command(yosys_cmd)
        else:
            # For local execution, create script file locally
            filename = os.path.join(work_dir, 'check.s')

            with open(filename, 'w') as f:
                f.write(full_cmd + '\n')
            return self._run_yosys_command(f'yosys -s {filename}')

    def _run_yosys_command(self, command: str) -> Tuple[int, str, str]:
        """
        Actually call 'yosys' either locally or via Docker.
        Return (exit_code, stdout, stderr).
        """
        # Print the exact LEC command being executed
        print(f'🔧 [LEC] Executing command: {command}')

        if self.use_docker and self.runner:
            # Docker execution
            try:
                rc, stdout, stderr = self.runner.run_cmd(command)
                return rc, stdout, stderr
            except Exception as e:
                self.error_message = f'Docker Yosys execution error: {e}'
                return 1, '', self.error_message
        else:
            # Local execution
            try:
                proc = subprocess.run(
                    command.split(),
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
