#!/usr/bin/env python3
"""
V2Chisel Batch Processing

This step processes multiple bugs from bug_lists_unified.yaml:
1. Reads bug list with unified Verilog diffs
2. For each bug, uses module_finder to locate corresponding Chisel modules
3. Eventually: LLM generates Chisel diffs, applies them, compiles, and runs LEC

Usage:
uv run python3 hagent/step/v2chisel_batch/v2chisel_batch.py -o output.yaml input.yaml
"""

import os
import sys
import argparse
import glob
import re
from pathlib import Path
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

# Set up environment for Runner (Docker execution mode)
os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

# Add project root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from hagent.core.step import Step
from hagent.core.llm_template import LLM_template
from hagent.core.llm_wrap import LLM_wrap
from hagent.tool.module_finder import Module_finder
from hagent.tool.docker_diff_applier import DockerDiffApplier
from hagent.tool.equiv_check import Equiv_check
from hagent.inou.builder import Builder

# Import components
try:
    from .components.bug_info import BugInfo
    from .components.hints_generator import HintsGenerator
    from .components.golden_design_builder import GoldenDesignBuilder
    from .components.baseline_verilog_generator import BaselineVerilogGenerator
except ImportError:
    # Fallback for direct execution or testing
    from components.bug_info import BugInfo
    from components.hints_generator import HintsGenerator
    from components.golden_design_builder import GoldenDesignBuilder
    from components.baseline_verilog_generator import BaselineVerilogGenerator


class V2chisel_batch(Step):
    """V2chisel_batch that runs REAL pipeline with real LLM calls"""

    def __init__(self):
        # Initialize parent class completely (this sets chisel_source_pattern and other required attributes)
        super().__init__()
        self.test_chisel_diff = None
        self.files_to_restore = []  # Track files that need restoration
        self.baseline_generated = False  # Track if we generated fresh baseline

        # Initialize Builder for automated Docker management
        self.builder = Builder(docker_image='mascucsc/hagent-simplechisel:2025.09r')

    def setup(self):
        """Initialize the batch processing step"""
        super().setup()
        # print(f'[V2chisel_batch] Input file: {self.input_file}')
        # print(f'[V2chisel_batch] Output file: {self.output_file}')

        # Initialize LLM components
        conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'v2chisel_batch_conf.yaml')
        if not os.path.exists(conf_file):
            self.error(f'Configuration file not found: {conf_file}')

        self.template_config = LLM_template(conf_file)

        # Configuration - set these early before LLM initialization
        self.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'  # Default pattern
        self.debug = True  # Enable debug output

        # Get LLM configuration from template config
        llm_config = self.template_config.template_dict.get('v2chisel_batch', {}).get('llm', {})

        # Allow override from input_data while keeping generic structure
        # Note: input LLM config is under v2chisel_batch.llm, not llm directly
        input_llm_config = self.input_data.get('v2chisel_batch', {}).get('llm', {})
        final_llm_config = {**llm_config, **input_llm_config}

        if self.debug:
            print(f'🔧 [DEBUG] Template LLM config: {llm_config}')
            print(f'🔧 [DEBUG] Input LLM config: {input_llm_config}')
            print(f'🔧 [DEBUG] Final LLM config: {final_llm_config}')

        # Use same pattern as working examples - pass complete config with LLM and prompts
        if final_llm_config:
            # Get the complete v2chisel_batch configuration (includes prompts)
            full_config = self.template_config.template_dict.get('v2chisel_batch', {})
            complete_config = {**full_config}  # Include all prompts
            complete_config['llm'] = final_llm_config  # Override LLM config

            self.lw = LLM_wrap(
                name='v2chisel_batch',
                log_file='v2chisel_batch.log',
                conf_file=conf_file,
                overwrite_conf=complete_config,
            )
        else:
            self.lw = LLM_wrap(name='v2chisel_batch', log_file='v2chisel_batch.log', conf_file=conf_file)

        if self.lw.last_error:
            raise ValueError(self.lw.last_error)

        # Show which model is being used
        # print('[V2chisel_batch] LLM components initialized')
        # print(f'[V2chisel_batch] Using model: {final_llm_config.get("model", "default")}')

        # Initialize module_finder
        self.module_finder = Module_finder()
        # print('[V2chisel_batch] Module_finder initialized')

        # Initialize HintsGenerator
        self.hints_generator = HintsGenerator(self.module_finder, builder=self.builder, debug=self.debug)
        # print('[V2chisel_batch] HintsGenerator initialized')

        # Initialize GoldenDesignBuilder
        self.golden_design_builder = GoldenDesignBuilder(self.builder, debug=self.debug)
        # print('[V2chisel_batch] GoldenDesignBuilder initialized')

        # Initialize BaselineVerilogGenerator
        self.baseline_verilog_generator = BaselineVerilogGenerator(self.builder, debug=self.debug)
        # print('[V2chisel_batch] BaselineVerilogGenerator initialized')

    def _run_docker_command(self, cmd_list, timeout=None):
        """Helper method to run Docker commands through Runner instead of subprocess

        Args:
            cmd_list: List of command parts (Docker, exec, container, command...)
            timeout: Timeout in seconds (warning: Runner doesn't support timeout)

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        if timeout:
            print(f'⚠️  Warning: timeout={timeout}s requested but not supported by Runner')

        # Convert Docker exec command list to Runner command
        # cmd_list format: ['docker', 'exec', container, 'bash', '-l', '-c', 'actual_command']
        if len(cmd_list) >= 4 and cmd_list[0] == 'docker' and cmd_list[1] == 'exec':
            # Skip docker, exec, container_name and use rest as command
            if len(cmd_list) >= 7 and cmd_list[3:6] == ['bash', '-l', '-c']:
                # This is a bash -l -c command - extract the actual command and use full SBT path
                command = cmd_list[6]
                # Fix SBT path and ensure proper quoting for runMain commands
                if 'sbt ' in command:
                    command = command.replace('sbt ', 'sbt ')
                    # Ensure runMain commands are properly quoted
                    if 'runMain' in command and '"runMain' not in command:
                        command = command.replace(
                            'sbt "runMain',
                            '/root/.cache/coursier/arc/https/github.com/sbt/sbt/releases/download/v1.11.5/sbt-1.11.5.zip/sbt/bin/sbt "runMain',
                        )
                        command = command.replace('runMain ', '"runMain ') + '"' if not command.endswith('"') else command
            else:
                # Join remaining command parts
                command = ' '.join(cmd_list[3:])

            return self.builder.run_cmd(command)
        else:
            # Fallback: join all parts (shouldn't happen with Docker commands)
            return self.builder.run_cmd(' '.join(cmd_list))

    def _compile_xiangshan(self, docker_container: str, force_compile: bool = True) -> dict:
        """Override parent compilation to fix permissions and use Runner"""
        print('🏗️  [COMPILE] Starting compilation with permission fixes...')

        try:
            # Step 1: Fix permissions on the repo directory
            print('🔧 [COMPILE] Fixing file permissions in container...')
            exit_code, stdout, stderr = self.builder.run_cmd('chown -R root:root /code/workspace/repo')
            if exit_code == 0:
                print('✅ [COMPILE] Fixed repository permissions')
            else:
                print(f'⚠️  [COMPILE] Permission fix warning: {stderr}')

            # Step 2: Clean any existing target directories that might have wrong permissions
            self.builder.run_cmd('rm -rf /code/workspace/repo/target /code/workspace/repo/project/target || true')
            print('🗑️ [COMPILE] Cleaned old target directories')

            # Step 3: Install SBT and try compilation
            print('📝 [COMPILE] Installing/ensuring SBT is available...')
            self.builder.run_cmd(
                'curl -fL https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz | gzip -d > /usr/local/bin/cs && chmod +x /usr/local/bin/cs'
            )
            self.builder.run_cmd('/usr/local/bin/cs install sbt')

            # Verify SBT is now available
            sbt_check_exit, sbt_check_out, sbt_check_err = self.builder.run_cmd('which sbt')
            print(f'SBT location: {sbt_check_out.strip()}')

            print('📝 [COMPILE] Running: sbt compile (via Runner with fixed permissions)')
            exit_code, stdout, stderr = self.builder.run_cmd("bash -l -c 'cd /code/workspace/repo && sbt compile'")

            if exit_code == 0:
                print('✅ [COMPILE] SBT compilation successful')
                return {'success': True, 'output': stdout, 'compilation_method': 'sbt_with_runner_and_permissions'}
            else:
                print(f'⚠️  [COMPILE] SBT failed: {stderr[:200]}...')

                # Step 4: Try Mill as fallback with Runner
                print('📝 [COMPILE] Trying Mill fallback via Runner...')
                exit_code2, stdout2, stderr2 = self.builder.run_cmd(
                    'bash -c "cd /code/workspace/repo && chmod +x ./mill && ./mill root.compile"'
                )

                if exit_code2 == 0:
                    print('✅ [COMPILE] Mill compilation successful')
                    return {'success': True, 'output': stdout2, 'compilation_method': 'mill_with_runner_and_permissions'}
                else:
                    print(f'⚠️  [COMPILE] Mill also failed: {stderr2[:200]}...')

            return {
                'success': False,
                'error': f'Both SBT and Mill failed. SBT: {stderr[:100]}... Mill: {stderr2[:100] if "stderr2" in locals() else "N/A"}...',
                'compilation_method': 'both_failed_with_runner',
            }

        except Exception as e:
            return {'success': False, 'error': f'Compilation exception: {str(e)}', 'compilation_method': 'exception'}

    def _generate_verilog_from_chisel(self, docker_container: str, module_name: str) -> dict:
        """Override parent Verilog generation to fix permissions and use Runner"""
        print('🔧 [VERILOG_GEN] Generating Verilog with permission fixes...')

        try:
            # Step 1: Fix permissions on the repo directory
            print('🔧 [VERILOG_GEN] Fixing file permissions in container...')
            exit_code, stdout, stderr = self.builder.run_cmd('chown -R root:root /code/workspace/repo')
            if exit_code == 0:
                print('✅ [VERILOG_GEN] Fixed repository permissions')
            else:
                print(f'⚠️  [VERILOG_GEN] Permission fix warning: {stderr}')

            # Step 2: Clean target directories and create fresh build dirs
            self.builder.run_cmd('rm -rf /code/workspace/repo/target /code/workspace/repo/project/target || true')
            self.builder.run_cmd('mkdir -p /code/workspace/build/build_singlecyclecpu_nd')
            print('🗑️ [VERILOG_GEN] Cleaned target directories and prepared build dirs')

            # Step 3: Try Verilog generation commands with Runner (same priority order as parent)
            generation_commands = [
                # DINO-specific SBT commands (HIGHEST PRIORITY - these work for DINO)
                {
                    'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
                    'name': 'SingleCycleCPUNoDebug',
                },
                {
                    'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.Main"',
                    'name': 'Main',
                },
                {
                    'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.pipelined.PipelinedDualIssueNoDebug"',
                    'name': 'PipelinedDualIssueNoDebug',
                },
                {
                    'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.PipelinedDualIssueNoDebug"',
                    'name': 'PipelinedDualIssueNoDebug_alt',
                },
                {
                    'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUDebug"',
                    'name': 'SingleCycleCPUDebug',
                },
                # Generic SBT commands (fallback for other projects)
                {
                    'cmd': 'cd /code/workspace/repo && sbt "runMain Main"',
                    'name': 'Generic_Main',
                },
                {
                    'cmd': f'cd /code/workspace/repo && sbt "runMain {module_name}"',
                    'name': f'Module_{module_name}',
                },
            ]

            tooling_errors = []
            for i, gen_cmd_info in enumerate(generation_commands):
                gen_cmd_str = gen_cmd_info['cmd']
                cmd_name = gen_cmd_info['name']

                print(f'     📝 Trying generation command {i + 1}: {cmd_name}')

                # Use Runner with bash -l -c for login shell
                exit_code, stdout, stderr = self.builder.run_cmd(f"bash -l -c '{gen_cmd_str}'")

                if exit_code == 0:
                    print(f'✅ [VERILOG_GEN] Verilog generation successful with command {i + 1}: {cmd_name}')

                    # Warn if we're not using the expected SingleCycleCPU command
                    if 'SingleCycleCPUNoDebug' not in gen_cmd_str:
                        print('⚠️  WARNING: Expected SingleCycleCPUNoDebug but used different command!')
                        print('           This may generate wrong CPU type for LEC comparison')

                    return {'success': True, 'output': stdout, 'command_used': gen_cmd_str, 'tooling_issue': False}
                else:
                    error_msg = stderr
                    print(f'     ❌ Command {i + 1} failed: {error_msg[:200]}...')

                    # Extra debug for SingleCycleCPUNoDebug failures
                    if 'SingleCycleCPUNoDebug' in gen_cmd_str:
                        print('     ⚠️  CRITICAL: SingleCycleCPUNoDebug failed! This should generate SingleCycleCPU')
                        print(f'     Error details: {error_msg[:300]}')

                    tooling_errors.append({'command': gen_cmd_str, 'error': error_msg})
                    continue

            return {
                'success': False,
                'error': 'All Verilog generation commands failed',
                'last_stderr': stderr if 'stderr' in locals() else 'No stderr available',
                'tooling_issue': True,
                'error_details': tooling_errors,
            }

        except Exception as e:
            return {'success': False, 'error': f'Verilog generation exception: {str(e)}', 'tooling_issue': True}

    def cleanup(self):
        """Override parent cleanup to use our Runner - but delay Docker cleanup until very end"""
        # Don't cleanup Docker container during the test - only at the very end
        # The golden design phase needs the container to still be running
        if hasattr(self, '_final_cleanup') and self._final_cleanup:
            print('🧹 [CLEANUP] Final cleanup - shutting down Docker container...')
            if self.builder:
                self.builder.cleanup()
        else:
            print('🔄 [CLEANUP] Deferring Docker cleanup - container still needed for golden design...')

        # Ensure all required attributes are set (in case parent init missed some)
        if not hasattr(self, 'chisel_source_pattern'):
            self.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'
        if not hasattr(self, 'module_finder'):
            self.module_finder = Module_finder()  # Initialize module finder properly
        if not hasattr(self, 'debug'):
            self.debug = True

        # Force set required attributes that parent class expects
        self.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'
        self.debug = True

        # Create mock template_config
        if not hasattr(self, 'template_config'):

            class MockTemplateConfig:
                def __init__(self):
                    self.template_dict = {'v2chisel_batch': {'llm': {'model': 'test', 'temperature': 0.1}}}

            self.template_config = MockTemplateConfig()

    def generate_fresh_baseline_verilog(self, docker_container=None):
        """Generate fresh baseline Verilog before any modifications"""
        print('🏭 [V2chisel_batch] Generating fresh baseline Verilog from pristine Chisel...')

        # Use Builder API - no need for container name since Builder handles this
        if docker_container is None:
            docker_container = 'hagent'  # Default fallback, but Builder API will handle this

        try:
            # Generate ONLY SingleCycleCPU to match what the gate design will be
            # Use Runner directly like the working cli_executor_simplechisel.py pattern
            print('🔧 [V2chisel_batch] Running: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')
            exit_code, stdout, stderr = self.builder.run_cmd(
                'bash -l -c \'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"\''
            )

            # Create compatibility object for existing code
            verilog_result = type('obj', (object,), {'returncode': exit_code, 'stderr': stderr, 'stdout': stdout})

            if verilog_result.returncode == 0:
                print('✅ [V2chisel_batch] Fresh baseline Verilog generated successfully')
                print('     Command used: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')

                # Copy generated files from build_singlecyclecpu_d to build_singlecyclecpu_nd
                # so they're available in the location the backup method expects
                copy_exit_code, copy_stdout, copy_stderr = self.builder.run_cmd(
                    'cp -r build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/ 2>/dev/null || true',
                    cwd='/code/workspace',
                )

                if copy_exit_code == 0:
                    print('✅ [V2chisel_batch] Copied baseline files to expected location')
                else:
                    print(f'⚠️  [V2chisel_batch] Copy had issues: {copy_stderr}')

                # DEBUG: Check what opcode is actually in the generated baseline
                debug_exit_code, debug_stdout, debug_stderr = self.builder.run_cmd(
                    'grep -n _signals_T_132 /code/workspace/build/build_singlecyclecpu_nd/Control.sv'
                )
                if debug_exit_code == 0:
                    print(f'🔍 [V2chisel_batch] Baseline contains: {debug_stdout.strip()}')
                else:
                    print(f'🔍 [V2chisel_batch] Could not find _signals_T_132 in baseline: {debug_stderr}')

                self.baseline_generated = True
                return True
            else:
                print('❌ [V2chisel_batch] Failed to generate fresh baseline:')
                print(f'     stdout: {verilog_result.stdout[-500:]}')  # Last 500 chars
                print(f'     stderr: {verilog_result.stderr[-500:]}')  # Last 500 chars
                return False

        except Exception as e:
            print(f'❌ [V2chisel_batch] Exception generating baseline: {e}')
            return False

    def track_file_for_restoration(self, file_path):
        """Track a file that needs to be restored after the test"""
        if file_path not in self.files_to_restore:
            self.files_to_restore.append(file_path)
            print(f'📝 [TRACK] Will restore: {file_path}')

    def restore_all_tracked_files(self):
        """Restore all files that were modified during the test"""
        print(f'🔄 [RESTORE] Restoring {len(self.files_to_restore)} modified files and cleaning Docker state...')

        try:
            # Step 1: Restore all tracked files using git checkout
            if self.files_to_restore:
                for file_path in self.files_to_restore:
                    # Convert Docker path to git-relative path
                    if file_path.startswith('/code/workspace/repo/'):
                        git_path = file_path.replace('/code/workspace/repo/', '')
                        exit_code, stdout, stderr = self.builder.run_cmd(
                            f'git checkout HEAD -- {git_path}', cwd='/code/workspace/repo'
                        )
                        if exit_code == 0:
                            print(f'     ✅ Restored: {git_path}')
                        else:
                            print(f'     ⚠️ Could not restore: {git_path}')

                print('✅ [RESTORE] All tracked source files restored')

            # Step 2: Clean SBT cache to prevent stale compilation artifacts
            print('🧹 [RESTORE] Cleaning SBT cache...')
            exit_code, stdout, stderr = self.builder.run_cmd("bash -l -c 'cd /code/workspace/repo && sbt clean'")
            if exit_code == 0:
                print('✅ [RESTORE] SBT cache cleaned')
            else:
                print(f'⚠️  [RESTORE] SBT clean failed: {stderr}')

            # Step 3: Remove generated Verilog files to ensure clean state
            print('🗑️ [RESTORE] Cleaning generated Verilog files...')
            self.builder.run_cmd(
                'rm -rf build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/* build/build_pipelined_d/* build/build_gcd/* || true',
                cwd='/code/workspace',
            )

            # Step 4: Remove golden directory
            self.builder.run_cmd('rm -rf lec_golden', cwd='/code/workspace/repo')
            print('✅ [RESTORE] Docker state fully cleaned - ready for next run')

            # Step 5: Final Docker container cleanup (now that we're completely done)
            print('🧹 [RESTORE] Final cleanup - shutting down Docker container...')
            self._final_cleanup = True  # Set flag to allow Docker cleanup
            if self.builder:
                self.builder.cleanup()
                print('✅ [RESTORE] Docker container shut down')

        except Exception as e:
            print(f'⚠️ [RESTORE] Warning: Could not restore some files: {e}')
            raise

    def _load_bug_list(self, bug_file_path: str) -> list:
        """Load and parse the bug_lists_unified.yaml file"""
        print(f'[V2chisel_batch] Loading bug list from: {bug_file_path}')

        if not os.path.exists(bug_file_path):
            self.error(f'Bug list file not found: {bug_file_path}')

        yaml = YAML()
        with open(bug_file_path, 'r') as f:
            data = yaml.load(f)

        if 'bugs' not in data:
            self.error('Invalid bug list format - missing "bugs" key')

        bugs = data['bugs']
        print(f'[V2chisel_batch] Loaded {len(bugs)} bugs from file')

        return bugs

    def _find_chisel_files_docker_filtered(self, container_name: str, docker_patterns: list, module_name: str = None) -> list:
        """Find Chisel files inside Docker container with smart filtering"""
        # Use Builder API instead of subprocess for container access

        print(f'[DEBUG] Searching for Chisel files for module: {module_name}')
        docker_files = []

        for pattern in docker_patterns:
            print(f'  🐳 Docker pattern: {pattern}')
            try:
                # OPTIMIZATION: Search for files containing the module name first
                if module_name:
                    print(f'  🔍 Pre-filtering for module: {module_name}')
                    # Use builder.run_cmd instead of subprocess
                    find_cmd = f"find {pattern} -name '*.scala' -type f -exec grep -il 'class.*{module_name}\\|object.*{module_name}' {{}} \\;"
                    exit_code, stdout, stderr = self.builder.run_cmd(find_cmd)

                    if exit_code == 0:
                        files = [f.strip() for f in stdout.split('\n') if f.strip()]
                        print(f'     ✅ Found {len(files)} files matching "{module_name}"')
                        for file in files[:3]:  # Show first 3
                            print(f'       - {file}')
                    else:
                        files = []
                        print(f'     ❌ No files found for module "{module_name}": {stderr}')

                    # If no matches with exact name, try broader search
                    if not files and len(module_name) > 3:
                        print('  🔍 Trying broader search with partial name...')
                        partial_name = module_name[:4] if len(module_name) > 4 else module_name
                        find_cmd = f"find {pattern} -name '*.scala' -type f -exec grep -il '{partial_name}' {{}} \\;"
                        exit_code, stdout, stderr = self.builder.run_cmd(find_cmd)
                        if exit_code == 0:
                            files = [f.strip() for f in stdout.split('\n') if f.strip()][:20]  # Limit to 20 files
                            print(f'     📋 Broader search found: {len(files)} files')
                        else:
                            files = []
                            print(f'     ❌ Broader search failed: {stderr}')
                else:
                    # Fallback: get all files (but limit to reasonable number)
                    find_cmd = f"find {pattern} -name '*.scala' -type f"
                    exit_code, stdout, stderr = self.builder.run_cmd(find_cmd)
                    if exit_code == 0:
                        all_files = [f.strip() for f in stdout.split('\n') if f.strip()]
                        # Limit to first 100 files to avoid performance issues
                        files = all_files[:100]
                        print(f'     📋 Fallback found: {len(all_files)} files, limited to: {len(files)} for performance')
                    else:
                        files = []
                        print(f'     ❌ Fallback search failed: {stderr}')

                if files:
                    for f in files[:3]:  # Show first 3
                        print(f'     - {f}')
                    if len(files) > 3:
                        print(f'     ... and {len(files) - 3} more')

                # Add docker: prefix to distinguish from local files
                # Use actual container name from builder instead of placeholder
                actual_container = 'builder_managed'  # Use a consistent name since we're using builder API
                docker_files.extend([f'docker:{actual_container}:{f}' for f in files])

            except Exception as e:
                print(f'     ❌ Error searching pattern {pattern}: {e}')
                pass

        return docker_files

    def _find_chisel_files_docker(self, container_name: str, docker_patterns: list) -> list:
        """Legacy method - use filtered version instead"""
        return self._find_chisel_files_docker_filtered(container_name, docker_patterns)

    def _find_verilog_files_in_docker(self, container_name: str, module_name: str) -> str:
        """Find actual Verilog files in Docker container to provide better module context"""
        try:
            # Use builder.run_cmd instead of subprocess for Docker operations
            exit_code, stdout, stderr = self.builder.run_cmd('find /code/workspace/build -name "*.sv" -type f')
            if exit_code != 0:
                print(f'❌ Failed to find Verilog files: {stderr}')
                return ''

            verilog_files = [f.strip() for f in stdout.strip().split('\n') if f.strip()]

            # print(f'Found {len(verilog_files)} Verilog files in Docker container')

            # Look for files that might match the module name
            matching_files = []
            for vfile in verilog_files:
                if module_name.lower() in vfile.lower():
                    matching_files.append(vfile)

            if matching_files:
                # print(f'Found {len(matching_files)} Verilog files matching "{module_name}":')
                for mf in matching_files[:3]:  # Show first 3
                    print(f'  - {mf}')

                # Read content from the first matching file to get module context
                try:
                    exit_code, stdout, stderr = self.builder.run_cmd(f'head -20 {matching_files[0]}')
                    if exit_code == 0:
                        return stdout
                except Exception:
                    pass
            else:
                print(f'No Verilog files found matching "{module_name}"')

        except Exception as e:
            print(f'❌ Failed to search Verilog files in Docker: {e}')

        return ''

    def _find_chisel_files(self, patterns=None) -> list:
        """Find Chisel source files using glob patterns (supports multiple patterns and Docker)"""
        import glob

        if patterns is None:
            patterns = [self.chisel_source_pattern]
        elif isinstance(patterns, str):
            patterns = [patterns]

        # print(f'[V2chisel_batch] Searching for Chisel files with {len(patterns)} pattern(s):')

        all_chisel_files = []

        # Check if Docker container specified
        docker_container = self.input_data.get('docker_container', 'hagent')
        docker_patterns = self.input_data.get('docker_patterns', ['/code/workspace/repo'])

        # Search in Docker first
        if docker_container:
            docker_files = self._find_chisel_files_docker(docker_container, docker_patterns)
            all_chisel_files.extend(docker_files)

        # Then search local patterns
        for pattern in patterns:
            if pattern.startswith('docker:'):
                continue  # Skip docker patterns in local search

            # print(f'  📁 Local pattern: {pattern}')
            files = glob.glob(pattern, recursive=True)
            print(f'     Found: {len(files)} files')

            if files:
                for f in files[:3]:  # Show first 3 per pattern
                    print(f'     - {f}')
                if len(files) > 3:
                    print(f'     ... and {len(files) - 3} more')
            else:
                print('     ⚠️  No files found')

            all_chisel_files.extend(files)

        # Remove duplicates while preserving order
        unique_files = []
        seen = set()
        for f in all_chisel_files:
            if f not in seen:
                unique_files.append(f)
                seen.add(f)

        print(f'[V2chisel_batch] Total unique Chisel files found: {len(unique_files)}')
        return unique_files

    def _read_docker_file(self, docker_path: str) -> str:
        """Read file content from Docker container using Builder API"""
        # Parse docker path: docker:container_name:file_path
        parts = docker_path.split(':', 2)
        if len(parts) != 3 or parts[0] != 'docker':
            raise ValueError(f'Invalid docker path format: {docker_path}')

        # parts[1] is container name - ignored since we use Builder API
        file_path = parts[2]

        try:
            # Use builder.run_cmd instead of subprocess
            exit_code, stdout, stderr = self.builder.run_cmd(f'cat {file_path}')
            if exit_code == 0:
                print(f'[DEBUG] Successfully read Docker file: {file_path}')
                return stdout
            else:
                raise Exception(f'Failed to read {file_path}: {stderr}')
        except Exception as e:
            raise Exception(f'Failed to read {file_path} from container via Builder API: {e}')

    def _prepare_files_for_module_finder(self, chisel_files: list) -> list:
        """Prepare file list for module_finder (handle Docker files)"""
        import tempfile
        import os

        prepared_files = []
        self.temp_files = []  # Keep track for cleanup

        for file_path in chisel_files:
            if file_path.startswith('docker:'):
                try:
                    # Read content from Docker
                    content = self._read_docker_file(file_path)

                    # Create temp file
                    temp_fd, temp_path = tempfile.mkstemp(suffix='.scala', prefix='docker_')
                    with os.fdopen(temp_fd, 'w') as f:
                        f.write(content)

                    self.temp_files.append(temp_path)
                    prepared_files.append(temp_path)

                    # Map temp path back to original for reporting
                    if not hasattr(self, 'temp_to_original'):
                        self.temp_to_original = {}
                    self.temp_to_original[temp_path] = file_path

                except Exception:
                    # print(f'     ⚠️  Failed to read Docker file {file_path}: {e}')
                    continue
            else:
                # Local file - use as is
                prepared_files.append(file_path)

        return prepared_files

    def _cleanup_temp_files(self):
        """Clean up temporary files created for Docker content"""
        import os

        if hasattr(self, 'temp_files'):
            for temp_file in self.temp_files:
                try:
                    os.unlink(temp_file)
                except OSError:
                    pass
            self.temp_files = []

    def _parse_metadata_from_rtl(self, docker_container: str, verilog_file: str, verilog_diff: str) -> dict:
        """Parse metadata from RTL files to extract Chisel file:line mappings"""

        # print(f'🔍 [METADATA FALLBACK] Parsing RTL metadata for: {verilog_file}')

        # Find the RTL file in build_debug
        rtl_path = f'/code/workspace/build/build_dbg/rtl/{verilog_file}'

        try:
            # Check if RTL file exists
            exit_code, _, _ = self.builder.run_cmd(f'test -f {rtl_path}')

            if exit_code != 0:
                # print(f'     ❌ RTL file not found: {rtl_path}')
                return {'success': False, 'error': 'RTL file not found'}

            # Read RTL file content using Builder's filesystem
            rtl_content = self.builder.filesystem.read_file(rtl_path)

            print(f'     ✅ Read RTL file: {len(rtl_content)} characters')

            # Extract metadata comments (format: // code/workspace/repo/path/file.scala:line:column)
            metadata_pattern = r'//\s*code/workspace/repo/([^:]+\.scala):(\d+):(\d+)'
            metadata_matches = re.findall(metadata_pattern, rtl_content)

            print(f'     📊 Found {len(metadata_matches)} metadata entries')

            # Group by file
            file_mappings = {}
            for file_path, line_num, col_num in metadata_matches:
                full_path = f'/code/workspace/repo/{file_path}'
                if full_path not in file_mappings:
                    file_mappings[full_path] = []
                file_mappings[full_path].append(int(line_num))

            # Show summary
            # print(f'     📁 Mapped to {len(file_mappings)} Chisel files:')
            for file_path, lines in list(file_mappings.items())[:3]:
                unique_lines = sorted(set(lines))
                print(f'       - {file_path}: {len(unique_lines)} lines')

            return {'success': True, 'file_mappings': file_mappings, 'total_metadata': len(metadata_matches)}

        except Exception as e:
            print(f'     ❌ Failed to read RTL file: {e}')
            return {'success': False, 'error': str(e)}

    def _extract_hints_from_metadata(self, docker_container: str, file_mappings: dict) -> str:
        """Extract actual Chisel code hints from metadata mappings"""
        # print(f'🔧 [METADATA FALLBACK] Extracting hints from {len(file_mappings)} files...')

        all_hints = []

        for file_path, line_numbers in file_mappings.items():
            try:
                # Read the Chisel file using Builder's filesystem
                file_content = self.builder.filesystem.read_file(file_path)
                file_lines = file_content.split('\n')

                # Get unique lines with context
                unique_lines = sorted(set(line_numbers))
                context_lines = set()

                for line_num in unique_lines:
                    # Add the line itself and some context (±2 lines)
                    for offset in range(-2, 3):
                        ctx_line = line_num + offset
                        if 1 <= ctx_line <= len(file_lines):
                            context_lines.add(ctx_line)

                # Format hints with line numbers
                file_hint_lines = []
                file_hint_lines.append(f'\n// From {file_path}')

                for line_num in sorted(context_lines):
                    line_content = file_lines[line_num - 1] if line_num <= len(file_lines) else ''
                    # Mark the original metadata lines with ->
                    marker = '->' if line_num in unique_lines else '  '
                    file_hint_lines.append(f'{marker} {line_num:4d}: {line_content}')

                all_hints.extend(file_hint_lines)
                print(f'     ✅ {file_path}: {len(unique_lines)} key lines, {len(context_lines)} total with context')

            except Exception as e:
                print(f'     ❌ Failed to read {file_path}: {e}')
                continue

        hints_text = '\n'.join(all_hints)
        # print(f'     📝 Generated {len(hints_text)} characters of hints')

        return hints_text

    def _get_metadata_fallback_hints(self, docker_container: str, verilog_file: str, verilog_diff: str) -> str:
        """Get hints using metadata fallback approach"""
        # print(f'🔄 [METADATA FALLBACK] Starting for {verilog_file}')

        # Parse metadata from RTL
        metadata_result = self._parse_metadata_from_rtl(docker_container, verilog_file, verilog_diff)

        if not metadata_result['success']:
            print(f'     ❌ Metadata parsing failed: {metadata_result.get("error", "Unknown error")}')
            return ''

        # Extract hints from mappings
        hints = self._extract_hints_from_metadata(docker_container, metadata_result['file_mappings'])

        if hints.strip():
            # print('     ✅ [METADATA FALLBACK] Generated hints successfully')
            return hints
        else:
            # print('     ❌ [METADATA FALLBACK] No hints generated')
            return ''

    def _call_llm_for_chisel_diff(
        self,
        verilog_diff: str,
        chisel_hints: str,
        attempt: int = 1,
        previous_diff: str = '',
        error_message: str = '',
        attempt_history: str = '',
    ) -> dict:
        """Call LLM to generate Chisel diff based on Verilog diff and hints"""
        print(f'🚀 [LLM_CALL] ENTERING _call_llm_for_chisel_diff (attempt {attempt})')
        print(f'🔧 [DEBUG] Verilog diff length: {len(verilog_diff)} characters')
        print(f'🔧 [DEBUG] Chisel hints length: {len(chisel_hints)} characters')

        # Choose prompt based on attempt and error type
        if attempt == 1:
            prompt_key = 'prompt_initial'
            template_data = {'verilog_diff': verilog_diff, 'chisel_hints': chisel_hints}
        elif 'compile' in error_message.lower() or 'compilation' in error_message.lower():
            prompt_key = 'prompt_compile_error'
            template_data = {
                'verilog_diff': verilog_diff,
                'previous_chisel_diff': previous_diff,
                'compile_error': error_message,
                'chisel_hints': chisel_hints,
            }
        elif 'lec' in error_message.lower() or 'equivalence' in error_message.lower():
            prompt_key = 'prompt_lec_error'
            template_data = {
                'verilog_diff': verilog_diff,
                'current_chisel_diff': previous_diff,
                'lec_error': error_message,
                'chisel_hints': chisel_hints,
            }
        elif attempt >= 4:
            prompt_key = 'prompt_final_attempt'
            template_data = {'verilog_diff': verilog_diff, 'attempt_history': attempt_history, 'chisel_hints': chisel_hints}
        else:
            # Default retry prompt (similar to initial)
            prompt_key = 'prompt_initial'
            template_data = {'verilog_diff': verilog_diff, 'chisel_hints': chisel_hints}

        try:
            # Get the prompt configuration
            full_config = self.template_config.template_dict.get('v2chisel_batch', {})
            if prompt_key not in full_config:
                return {'success': False, 'error': f'Prompt {prompt_key} not found in config'}

            prompt_section = full_config[prompt_key]
            prompt_template = LLM_template(prompt_section)

            # Update LLM wrapper with new template
            self.lw.chat_template = prompt_template
            self.lw.name = f'v2chisel_batch_attempt_{attempt}'

            print(f'     🎯 Using prompt: {prompt_key}')
            print(f'     📝 Template data keys: {list(template_data.keys())}')

            # Call LLM
            print(f"🔍 DEBUG: About to call LLM inference with prompt_key='{prompt_key}', n=1")
            print(f'🔍 DEBUG: Template data has keys: {list(template_data.keys())}')
            response_list = self.lw.inference(template_data, prompt_index=prompt_key, n=1)
            print(
                f"🔍 DEBUG: LLM inference returned: {type(response_list)}, len={len(response_list) if response_list else 'None'}"
            )

            # Check for LLM errors first
            if self.lw.last_error:
                print(f'🔍 DEBUG: LLM error detected: {self.lw.last_error}')
                return {'success': False, 'error': f'LLM error: {self.lw.last_error}'}

            if not response_list or not response_list[0].strip():
                print(f'🔍 DEBUG: Empty LLM response - response_list: {response_list}')
                return {'success': False, 'error': 'LLM returned empty response'}

            generated_diff = response_list[0].strip()

            # Clean up markdown fences if present
            if '```' in generated_diff:
                lines = generated_diff.split('\n')
                cleaned_lines = []
                in_code_block = False

                for line in lines:
                    if line.strip().startswith('```'):
                        in_code_block = not in_code_block
                        continue
                    if in_code_block or not line.strip().startswith('```'):
                        cleaned_lines.append(line)

                generated_diff = '\n'.join(cleaned_lines).strip()

            # print(f'     ✅ LLM generated diff: {len(generated_diff)} characters')
            # if self.debug:
            #     print('     📋 COMPLETE Generated diff:')
            #     print('=' * 80)
            #     print(generated_diff)
            #     print('=' * 80)

            return {'success': True, 'chisel_diff': generated_diff, 'prompt_used': prompt_key, 'attempt': attempt}

        except Exception as e:
            # print(f'     ❌ LLM call failed: {e}')
            return {'success': False, 'error': str(e)}

    def _create_master_backup(self, docker_container: str, chisel_diff: str) -> dict:
        """Create MASTER backup of original files at the start of bug processing - this is the ONLY backup we keep"""
        # print('💾 [MASTER_BACKUP] Creating master backup of original files...')

        try:
            import re
            import time

            # Parse the diff to find files that will be modified throughout ALL iterations
            files_to_backup = set()
            diff_lines = chisel_diff.split('\n')

            for line in diff_lines:
                # Look for unified diff file headers: --- a/path/file.scala or +++ b/path/file.scala
                if line.startswith('---') or line.startswith('+++'):
                    # Extract file path
                    match = re.search(r'[ab]/(.*\.scala)', line)
                    if match:
                        file_path = match.group(1)
                        # Convert relative path to absolute path in container
                        if not file_path.startswith('/code/workspace/repo/'):
                            file_path = f'/code/workspace/repo/{file_path}'
                        files_to_backup.add(file_path)

            # Create MASTER backup directory (this will persist for the entire bug processing)
            backup_id = f'master_backup_{int(time.time())}'
            backup_dir = f'/tmp/chisel_master_backup_{backup_id}'

            # Create backup directory in container
            exit_code, _, _ = self.builder.run_cmd(f'mkdir -p {backup_dir}')
            if exit_code != 0:
                raise Exception(f'Failed to create backup directory {backup_dir}')

            backed_up_files = []

            if not files_to_backup:
                print('     ⚠️  No Scala files found in diff - will create backup for original Verilog only')
            for file_path in files_to_backup:
                # Check if file exists before backing up
                check_exit_code, _, _ = self.builder.run_cmd(f'test -f {file_path}')

                if check_exit_code == 0:
                    # File exists - back it up to MASTER backup
                    backup_file_path = f'{backup_dir}/{file_path.replace("/", "_")}.original'
                    cp_exit_code, _, _ = self.builder.run_cmd(f'cp {file_path} {backup_file_path}')

                    if cp_exit_code == 0:
                        backed_up_files.append({'original_path': file_path, 'backup_path': backup_file_path})
                        # print(f'     ✅ Master backup created: {file_path}')
                    else:
                        pass  # Backup failed, continuing
                else:
                    print(f'     ⚠️  File does not exist (new file?): {file_path}')

            # print(f'💾 [MASTER_BACKUP] Created master backup with ID: {backup_id} ({len(backed_up_files)} files)')
            # print('     🔒 This backup will be used for ALL restore operations until LEC success')

            # NEW: Backup existing original Verilog files for LEC golden design using BaselineVerilogGenerator
            # print('📁 [ORIGINAL_VERILOG] Backing up existing original Verilog files for LEC golden design...')
            baseline_verilog_result = self.baseline_verilog_generator.backup_baseline_verilog(backup_id)

            # DEBUG: Show what we got from the backup process
            # print('🔍 [DEBUG] Original Verilog backup result:')
            # print(f'     Success: {baseline_verilog_result.get("success", False)}')
            # print(f'     Files found: {len(baseline_verilog_result.get("files", {}))}')
            # if baseline_verilog_result.get('files'):
            #     for orig_path, backup_path in baseline_verilog_result.get('files', {}).items():
            #         print(f'       - {orig_path} -> {backup_path}')
            # if not baseline_verilog_result.get('success', False):
            #     print(f'     Error: {baseline_verilog_result.get("error", "Unknown error")}')

            return {
                'success': True,
                'backup_id': backup_id,
                'backup_dir': backup_dir,
                'files_backed_up': backed_up_files,
                'original_verilog_files': baseline_verilog_result.get('files', {}),
                'baseline_verilog_success': baseline_verilog_result.get('success', False),
                'is_master_backup': True,
            }

        except Exception as e:
            error_msg = f'Master backup creation failed: {str(e)}'
            print(f'❌ [MASTER_BACKUP] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _create_file_backup(self, docker_container: str, chisel_diff: str) -> dict:
        """Create backup of files that will be modified by the diff"""
        print('💾 [BACKUP] Creating file backup before applying diff...')

        try:
            import subprocess
            import re
            import time

            # Parse the diff to find files that will be modified
            files_to_backup = set()
            diff_lines = chisel_diff.split('\n')

            for line in diff_lines:
                # Look for unified diff file headers: --- a/path/file.scala or +++ b/path/file.scala
                if line.startswith('---') or line.startswith('+++'):
                    # Extract file path
                    match = re.search(r'[ab]/(.*\.scala)', line)
                    if match:
                        file_path = match.group(1)
                        # Convert relative path to absolute path in container
                        if not file_path.startswith('/code/workspace/repo/'):
                            file_path = f'/code/workspace/repo/{file_path}'
                        files_to_backup.add(file_path)

            if not files_to_backup:
                print('     ⚠️  No Scala files found in diff - skipping backup')
                return {'success': True, 'files_backed_up': [], 'backup_id': None}

            # Create unique backup directory with timestamp
            backup_id = f'backup_{int(time.time())}'
            backup_dir = f'/tmp/chisel_backup_{backup_id}'

            # Create backup directory in container
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            subprocess.run(mkdir_cmd, check=True)

            backed_up_files = []
            for file_path in files_to_backup:
                # Check if file exists before backing up
                check_cmd = ['docker', 'exec', docker_container, 'test', '-f', file_path]
                check_result = subprocess.run(check_cmd, capture_output=True)

                if check_result.returncode == 0:
                    # File exists - back it up
                    backup_file_path = f'{backup_dir}/{file_path.replace("/", "_")}.backup'
                    cp_cmd = ['docker', 'exec', docker_container, 'cp', file_path, backup_file_path]
                    cp_result = subprocess.run(cp_cmd, capture_output=True, text=True)

                    if cp_result.returncode == 0:
                        backed_up_files.append({'original_path': file_path, 'backup_path': backup_file_path})
                        # print(f'     ✅ Backed up: {file_path}')
                    else:
                        pass  # Backup failed, continuing
                else:
                    print(f'     ⚠️  File does not exist (new file?): {file_path}')

            print(f'💾 [BACKUP] Created backup with ID: {backup_id} ({len(backed_up_files)} files)')
            return {'success': True, 'backup_id': backup_id, 'backup_dir': backup_dir, 'files_backed_up': backed_up_files}

        except Exception as e:
            error_msg = f'Backup creation failed: {str(e)}'
            print(f'❌ [BACKUP] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _restore_to_original(self, docker_container: str, master_backup_info: dict, reason: str = 'failure') -> dict:
        """Restore files to ORIGINAL pristine state from master backup"""
        if not master_backup_info or not master_backup_info.get('success') or not master_backup_info.get('files_backed_up'):
            return {'success': True, 'message': 'No master backup to restore from'}

        print(f'🔄 [RESTORE_TO_ORIGINAL] Restoring to pristine state due to: {reason}')
        print(f'     🔒 Using master backup: {master_backup_info["backup_id"]}')
        print(f'     📁 Files to restore: {len(master_backup_info.get("files_backed_up", []))}')

        try:
            import subprocess

            restored_files = []
            for file_info in master_backup_info['files_backed_up']:
                original_path = file_info['original_path']
                backup_path = file_info['backup_path']

                # DEBUG: Check if backup file exists
                check_cmd = ['docker', 'exec', docker_container, 'test', '-f', backup_path]
                check_result = subprocess.run(check_cmd, capture_output=True)
                if check_result.returncode != 0:
                    print(f'     ❌ Backup file does not exist: {backup_path}')
                    continue

                # Restore the file from MASTER backup (original state)
                cp_cmd = ['docker', 'exec', docker_container, 'cp', backup_path, original_path]
                cp_result = subprocess.run(cp_cmd, capture_output=True, text=True)

                if cp_result.returncode == 0:
                    restored_files.append(original_path)
                    print(f'     ✅ Restored to original: {original_path}')

                    # DEBUG: Verify restoration worked by showing first few lines
                    verify_cmd = ['docker', 'exec', docker_container, 'head', '-3', original_path]
                    verify_result = subprocess.run(verify_cmd, capture_output=True, text=True)
                    if verify_result.returncode == 0:
                        first_line = verify_result.stdout.split('\n')[0]
                        print(f'          First line now: {first_line}')
                else:
                    print(f'     ❌ Failed to restore {original_path}: {cp_result.stderr}')

            print(f'🔄 [RESTORE_TO_ORIGINAL] Restored {len(restored_files)} files to pristine state')
            return {'success': True, 'restored_files': restored_files, 'restore_reason': reason}

        except Exception as e:
            error_msg = f'Restore to original failed: {str(e)}'
            print(f'❌ [RESTORE_TO_ORIGINAL] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _restore_from_backup(self, docker_container: str, backup_info: dict) -> dict:
        """Restore files from backup after failed compilation"""
        if not backup_info or not backup_info.get('success') or not backup_info.get('files_backed_up'):
            return {'success': True, 'message': 'No backup to restore'}

        print(f'🔄 [RESTORE] Restoring from backup: {backup_info["backup_id"]}')

        try:
            import subprocess

            restored_files = []
            for file_info in backup_info['files_backed_up']:
                original_path = file_info['original_path']
                backup_path = file_info['backup_path']

                # Restore the file
                cp_cmd = ['docker', 'exec', docker_container, 'cp', backup_path, original_path]
                cp_result = subprocess.run(cp_cmd, capture_output=True, text=True)

                if cp_result.returncode == 0:
                    restored_files.append(original_path)
                    print(f'     ✅ Restored: {original_path}')
                else:
                    print(f'     ❌ Failed to restore {original_path}: {cp_result.stderr}')

            print(f'🔄 [RESTORE] Restored {len(restored_files)} files successfully')
            return {'success': True, 'restored_files': restored_files}

        except Exception as e:
            error_msg = f'Restore failed: {str(e)}'
            print(f'❌ [RESTORE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _cleanup_master_backup(self, docker_container: str, master_backup_info: dict) -> None:
        """Clean up master backup directory ONLY after successful LEC (full pipeline success)"""
        if not master_backup_info or not master_backup_info.get('success') or not master_backup_info.get('backup_dir'):
            return

        try:
            import subprocess

            backup_dir = master_backup_info['backup_dir']
            rm_cmd = ['docker', 'exec', docker_container, 'rm', '-rf', backup_dir]
            subprocess.run(rm_cmd, capture_output=True)
            print(f'🗑️  [CLEANUP] Removed master backup: {master_backup_info["backup_id"]} (LLM changes accepted)')
        except Exception as e:
            print(f'⚠️  [CLEANUP] Failed to remove master backup: {e}')

    def _cleanup_backup(self, docker_container: str, backup_info: dict) -> None:
        """Clean up backup directory after successful compilation"""
        if not backup_info or not backup_info.get('success') or not backup_info.get('backup_dir'):
            return

        try:
            import subprocess

            backup_dir = backup_info['backup_dir']
            rm_cmd = ['docker', 'exec', docker_container, 'rm', '-rf', backup_dir]
            subprocess.run(rm_cmd, capture_output=True)
            print(f'🗑️  [CLEANUP] Removed backup: {backup_info["backup_id"]}')
        except Exception as e:
            print(f'⚠️  [CLEANUP] Failed to remove backup: {e}')

    def _apply_chisel_diff(self, chisel_diff: str, docker_container: str) -> dict:
        """Apply generated Chisel diff to Docker container with backup support"""
        # print('🔧 [APPLIER] Starting diff application...')

        try:
            applier = DockerDiffApplier(self.builder)
            success = applier.apply_diff_to_container(chisel_diff, dry_run=False)

            if success:
                # print('✅ [APPLIER] Successfully applied Chisel diff to container')
                return {'success': True}
            else:
                # print('❌ [APPLIER] Failed to apply Chisel diff')
                return {'success': False, 'error': 'Diff application failed - could not find removal lines'}
        except Exception as e:
            error_msg = str(e)
            # print(f'❌ [APPLIER] Error applying diff: {error_msg}')
            return {'success': False, 'error': error_msg}

    def _ensure_main_object_exists(self, docker_container: str, module_name: str = None) -> dict:
        """Ensure a Main object exists for Verilog generation"""
        print('🔍 [MAIN_CHECK] Checking for Main object...')

        try:
            # Check if Main.scala or similar already exists using Builder API
            find_cmd_str = 'find /code/workspace/repo/src -name "*.scala" -exec grep -l "object Main" {} \;'

            exit_code, stdout, stderr = self.builder.run_cmd(find_cmd_str)

            if exit_code == 0 and stdout.strip():
                print('✅ [MAIN_CHECK] Main object already exists')
                existing_files = stdout.strip().split('\n')
                return {'success': True, 'main_exists': True, 'files': existing_files}

            # Main object doesn't exist - create one
            print('🔧 [MAIN_CHECK] Creating Main object for Verilog generation...')

            # Determine the top module based on module_name or use generic approach
            if module_name:
                top_module = module_name
            else:
                # Try to find the top module from existing code using Builder API
                grep_cmd_str = 'grep -r -l "class.*extends.*Module" /code/workspace/repo/src'
                grep_exit_code, grep_stdout, grep_stderr = self.builder.run_cmd(grep_cmd_str)

                if grep_exit_code == 0 and grep_stdout.strip():
                    # Use a generic approach
                    top_module = 'Top'  # Default
                else:
                    top_module = 'Top'  # Fallback

            # Create Main.scala content
            main_content = f"""package object MainGen extends App {{
    import chisel3._
    import chisel3.stage.ChiselStage
    import circt.stage._
    
    // Auto-generated Main object for Verilog generation
    // You may need to adjust the Top module and config based on your design
    
    ChiselStage.emitSystemVerilogFile(
      new {top_module}(), // Adjust this to your actual top module
      firtoolOpts = Array(
        "-disable-all-randomization",
        "--lowering-options=disallowPackedArrays,disallowLocalVariables"
      )
    )
}}
"""

            # Write the Main.scala file using Builder filesystem API
            main_file_path = '/code/workspace/repo/src/main/scala/MainGen.scala'

            # Write the file using Builder filesystem API instead of subprocess
            try:
                self.builder.filesystem.write_file(main_file_path, main_content)
                print('✅ [MAIN_CHECK] Main object created successfully')
                return {'success': True, 'main_exists': False, 'created_file': main_file_path, 'top_module': top_module}
            except Exception as write_error:
                return {'success': False, 'error': f'Failed to create Main object: {str(write_error)}'}

        except Exception as e:
            return {'success': False, 'error': f'Main object check error: {str(e)}'}

    def _generate_verilog_from_chisel(self, docker_container: str, module_name: str) -> dict:
        """Generate Verilog from Chisel code after compilation"""
        print('🔧 [VERILOG_GEN] Generating Verilog from compiled Chisel...')

        # For DINO project, skip Main object creation as it has its own main objects
        print('⚠️  [VERILOG_GEN] Skipping MainGen.scala creation for DINO project (uses existing main objects)')

        try:
            # Try different Verilog generation commands based on the project
            # Prioritize DINO-specific commands first, then fallbacks
            generation_commands = [
                # DINO-specific SBT commands (HIGHEST PRIORITY - these work for DINO)
                # SingleCycleCPU first to match the desired CPU type
                'bash -l -c "cd /code/workspace/repo && sbt \\"runMain dinocpu.SingleCycleCPUNoDebug\\""',
                'bash -l -c "cd /code/workspace/repo && sbt \\"runMain dinocpu.Main\\""',
                'bash -l -c "cd /code/workspace/repo && sbt \\"runMain dinocpu.pipelined.PipelinedDualIssueNoDebug\\""',
                'bash -l -c "cd /code/workspace/repo && sbt \\"runMain dinocpu.PipelinedDualIssueNoDebug\\""',
                'bash -l -c "cd /code/workspace/repo && sbt \\"runMain dinocpu.SingleCycleCPUDebug\\""',
                # Generic SBT commands (fallback for other projects)
                'bash -l -c "cd /code/workspace/repo && sbt \\"runMain Main\\""',
                f'bash -l -c "cd /code/workspace/repo && sbt \\"runMain {module_name}\\""',
                f'bash -l -c "cd /code/workspace/repo && sbt \\"runMain dinocpu.{module_name}\\""',
                f'bash -l -c "cd /code/workspace/repo && sbt \\"runMain xiangshan.{module_name}\\""',
                # Mill commands (only try if sbt project doesn't work)
                'bash -c "cd /code/workspace/repo && ./mill root.runMain Main"',
                f'bash -c "cd /code/workspace/repo && ./mill root.runMain {module_name}"',
            ]

            tooling_errors = []
            for i, gen_cmd_str in enumerate(generation_commands):
                print(f'     📝 Trying generation command {i + 1}: {gen_cmd_str.split("&&")[-1].strip()}')

                exit_code, stdout, stderr = self.builder.run_cmd(gen_cmd_str)

                if exit_code == 0:
                    print(f'✅ [VERILOG_GEN] Verilog generation successful with command {i + 1}')
                    print(f'     Successful command: {gen_cmd_str.split("&&")[-1].strip()}')

                    # Warn if we're not using the expected SingleCycleCPU command
                    if 'SingleCycleCPUNoDebug' not in gen_cmd_str:
                        print('⚠️  WARNING: Expected SingleCycleCPUNoDebug but used different command!')
                        print('           This may generate wrong CPU type for LEC comparison')
                    return {'success': True, 'output': stdout, 'command_used': gen_cmd_str, 'tooling_issue': False}
                else:
                    error_msg = stderr
                    print(f'     ❌ Command {i + 1} failed: {error_msg[:200]}...')

                    # Extra debug for SingleCycleCPUNoDebug failures
                    if 'SingleCycleCPUNoDebug' in gen_cmd_str:
                        print('     ⚠️  CRITICAL: SingleCycleCPUNoDebug failed! This should generate SingleCycleCPU')
                        print(f'     Error details: {error_msg[:300]}')

                    # Classify the error type - expanded to catch more tooling issues
                    is_tooling_error = any(
                        keyword in error_msg.lower()
                        for keyword in [
                            # Command/file not found issues
                            'command not found',
                            'no such file',
                            'file not found',
                            'permission denied',
                            # Main class/object issues (these are tooling, not Chisel diff issues)
                            'could not find or load main class',
                            'class not found',
                            'classnotfoundexception',
                            'main method not found',
                            'no main manifest attribute',
                            'main class',
                            # Build tool specific errors (VERY CLEAR tooling issues)
                            'no build file',
                            'build.mill',
                            'build.sc',
                            'mill project',
                            'sbt project',
                            'mill',
                            'sbt',
                            'build failed',
                            'compilation failed',
                            # Import/dependency issues (often tooling related)
                            'object chiselstage is not a member',
                            'package chisel3.stage',
                            'import chisel3.stage',
                            'chiselstage',
                            'firtoolOpts',
                            # General tooling indicators
                            'java.lang.',
                            'scala.',
                            'at java.',
                            'caused by:',
                            'exception in thread',
                        ]
                    )

                    tooling_errors.append({'command': gen_cmd_str, 'error': error_msg, 'is_tooling_error': is_tooling_error})
                    continue

            # All generation commands failed - determine if it's a tooling issue
            # If ALL commands failed with tooling errors, or if we have multiple different types of
            # tooling errors, it's almost certainly a tooling/config issue, not a Chisel diff issue
            all_tooling_errors = all(err['is_tooling_error'] for err in tooling_errors)
            mostly_tooling_errors = sum(1 for err in tooling_errors if err['is_tooling_error']) >= len(tooling_errors) * 0.7

            # Determine if it's a tooling issue - be more aggressive about detecting tooling problems
            # ANY of these conditions indicates tooling issue:
            # 1. ALL errors are tooling errors
            # 2. At least 50% are tooling errors (was 70%, too strict)
            # 3. ANY error contains critical tooling indicators
            critical_tooling_indicators = [
                'no build file',
                'build.mill',
                'build.sc',
                'could not find or load main class',
                'main class',
            ]
            has_critical_tooling_error = any(
                any(indicator in err['error'].lower() for indicator in critical_tooling_indicators) for err in tooling_errors
            )

            is_tooling_failure = (
                all_tooling_errors
                or mostly_tooling_errors  # 70% still applies
                or (
                    sum(1 for err in tooling_errors if err['is_tooling_error']) >= len(tooling_errors) * 0.5
                )  # NEW: 50% threshold
                or has_critical_tooling_error
            )  # NEW: Critical indicators

            tooling_count = sum(1 for err in tooling_errors if err['is_tooling_error'])
            print(f'     🔍 Tooling error analysis: {tooling_count}/{len(tooling_errors)} commands had tooling errors')

            if is_tooling_failure:
                print('     🔧 This appears to be a tooling/configuration issue')
                if has_critical_tooling_error:
                    print('     🎯 CRITICAL tooling error detected (build file, main class, etc.)')
                elif all_tooling_errors:
                    print('     📊 ALL commands failed with tooling errors')
                elif mostly_tooling_errors:
                    print('     📊 70%+ commands failed with tooling errors')
                elif tooling_count >= len(tooling_errors) * 0.5:
                    print('     📊 50%+ commands failed with tooling errors')
            else:
                print('     🤖 This might be related to the Chisel diff generated by LLM')
                print('     🕰 Hint: If you see build file or main class errors above, this classification might be wrong')

            return {
                'success': False,
                'error': 'All Verilog generation commands failed',
                'last_stderr': tooling_errors[-1]['error'] if tooling_errors else 'No stderr available',
                'tooling_issue': is_tooling_failure,
                'error_details': tooling_errors,
                'tooling_analysis': {
                    'total_commands': len(tooling_errors),
                    'tooling_errors': tooling_count,
                    'tooling_percentage': (tooling_count / len(tooling_errors) * 100) if tooling_errors else 0,
                    'has_critical_tooling_error': has_critical_tooling_error,
                    'classified_as_tooling': is_tooling_failure,
                    'classification_reason': (
                        'critical_tooling_error'
                        if has_critical_tooling_error
                        else 'all_tooling_errors'
                        if all_tooling_errors
                        else 'mostly_tooling_errors_70'
                        if mostly_tooling_errors
                        else 'mostly_tooling_errors_50'
                        if tooling_count >= len(tooling_errors) * 0.5
                        else 'insufficient_tooling_indicators'
                    ),
                },
            }

        except Exception as timeout_error:
            if 'timeout' in str(timeout_error).lower():
                return {'success': False, 'error': 'Verilog generation timeout (5 minutes)', 'tooling_issue': True}
            else:
                raise
        except Exception as e:
            return {'success': False, 'error': f'Verilog generation error: {str(e)}', 'tooling_issue': True}

    def _generate_baseline_verilog(self, docker_container: str, backup_id: str) -> dict:
        """Generate baseline Verilog from original (unmodified) Chisel code for LEC golden design"""
        try:
            print('⚡ [BASELINE] Generating baseline Verilog from pristine Chisel code...')

            # Use same generation logic as _generate_verilog_from_chisel but for baseline
            # We assume the Chisel code is currently in its original state (before any diff application)
            result = self._generate_verilog_from_chisel(docker_container, 'dinocpu')

            if not result['success']:
                print(f'⚠️  [BASELINE] Failed to generate baseline Verilog: {result.get("error", "Unknown error")}')
                print('     LEC will be skipped due to baseline generation failure')
                return {'success': False, 'error': f'Baseline generation failed: {result.get("error", "Unknown")}'}

            print('✅ [BASELINE] Baseline Verilog generated successfully')

            # Find all generated Verilog files in the container
            print('📁 [BASELINE] Finding and backing up generated Verilog files...')
            verilog_files = self._find_and_backup_verilog_files(docker_container, backup_id)

            if verilog_files:
                print(f'✅ [BASELINE] Backed up {len(verilog_files)} baseline Verilog files')
                return {
                    'success': True,
                    'files': verilog_files,
                    'generation_output': result.get('output', ''),
                    'command_used': result.get('command_used', ''),
                }
            else:
                print('⚠️  [BASELINE] No Verilog files found after generation')
                return {'success': False, 'error': 'No Verilog files found after baseline generation'}

        except Exception as e:
            error_msg = f'Baseline Verilog generation failed: {str(e)}'
            print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _backup_existing_original_verilog(self, docker_container: str, backup_id: str) -> dict:
        """Backup existing original Verilog files from /code/workspace/build/build_singlecyclecpu_nd/ for LEC golden design"""
        try:
            import subprocess

            print('📁 [ORIGINAL_VERILOG] Finding existing original Verilog files...')

            # The corrected path to existing original Verilog files - use singlecyclecpu_nd to match SingleCycleCPUNoDebug
            original_verilog_path = '/code/workspace/build/build_singlecyclecpu_nd'

            # Find all .sv files in the original Verilog directory
            find_cmd = ['docker', 'exec', docker_container, 'find', original_verilog_path, '-name', '*.sv', '-type', 'f']
            find_result = subprocess.run(find_cmd, capture_output=True, text=True, timeout=30)

            if find_result.returncode != 0 or not find_result.stdout.strip():
                print(f'❌ [ORIGINAL_VERILOG] No original Verilog files found in {original_verilog_path}')
                return {'success': False, 'files': {}, 'error': f'No original Verilog files found in {original_verilog_path}'}

            original_verilog_files = [f.strip() for f in find_result.stdout.strip().split('\n') if f.strip()]
            print(f'📁 [ORIGINAL_VERILOG] Found {len(original_verilog_files)} original Verilog files:')
            for vf in original_verilog_files:
                print(f'     - {vf}')

            # Create backup directory for original Verilog
            backup_dir = f'/tmp/original_verilog_backup_{backup_id}'
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            subprocess.run(mkdir_cmd, check=True)

            # Backup each original Verilog file
            backed_up_files = {}
            for verilog_file in original_verilog_files:
                filename = verilog_file.split('/')[-1]  # Extract filename
                backup_path = f'{backup_dir}/{filename}'

                # Copy original to backup location
                cp_cmd = ['docker', 'exec', docker_container, 'cp', verilog_file, backup_path]
                cp_result = subprocess.run(cp_cmd, capture_output=True)

                if cp_result.returncode == 0:
                    backed_up_files[verilog_file] = backup_path  # container_path -> backup_path
                    print(f'     ✅ Backed up original Verilog: {filename}')
                else:
                    print(f'     ❌ Failed to backup {filename}')

            if backed_up_files:
                print(f'✅ [ORIGINAL_VERILOG] Successfully backed up {len(backed_up_files)} original Verilog files')
                return {
                    'success': True,
                    'files': backed_up_files,
                    'backup_dir': backup_dir,
                    'original_path': original_verilog_path,
                }
            else:
                print('❌ [ORIGINAL_VERILOG] No original Verilog files were successfully backed up')
                return {'success': False, 'files': {}, 'error': 'No files were successfully backed up'}

        except Exception as e:
            error_msg = f'Original Verilog backup failed: {str(e)}'
            print(f'❌ [ORIGINAL_VERILOG] {error_msg}')
            return {'success': False, 'files': {}, 'error': error_msg}

    def _find_and_backup_verilog_files(self, docker_container: str, backup_id: str) -> dict:
        """Find generated Verilog files and back them up for later use in golden design creation"""
        try:
            import subprocess

            # Search for .sv files in common generation locations
            search_paths = ['/code/workspace/repo', '/code/workspace/build', '/code/workspace']

            found_files = {}
            backup_dir = f'/tmp/baseline_verilog_{backup_id}'

            # Create backup directory for baseline Verilog
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            subprocess.run(mkdir_cmd, check=True)

            for search_path in search_paths:
                try:
                    # Find .sv files
                    find_cmd = ['docker', 'exec', docker_container, 'find', search_path, '-name', '*.sv', '-type', 'f']
                    find_result = subprocess.run(find_cmd, capture_output=True, text=True, timeout=30)

                    if find_result.returncode == 0 and find_result.stdout.strip():
                        verilog_files = [f.strip() for f in find_result.stdout.strip().split('\n') if f.strip()]

                        for verilog_file in verilog_files:
                            # Extract filename for backup
                            filename = verilog_file.split('/')[-1]
                            backup_path = f'{backup_dir}/{filename}'

                            # Copy to backup location
                            cp_cmd = ['docker', 'exec', docker_container, 'cp', verilog_file, backup_path]
                            cp_result = subprocess.run(cp_cmd, capture_output=True)

                            if cp_result.returncode == 0:
                                found_files[verilog_file] = backup_path
                                print(f'     ✅ Backed up baseline Verilog: {filename}')
                            else:
                                print(f'     ⚠️  Failed to backup {filename}')

                except subprocess.TimeoutExpired:
                    print(f'     ⚠️  Search timeout in {search_path}')
                    continue
                except Exception as e:
                    print(f'     ⚠️  Search error in {search_path}: {str(e)}')
                    continue

            return found_files

        except Exception as e:
            print(f'❌ [BASELINE] Error finding/backing up Verilog files: {str(e)}')
            return {}

    def _ensure_pristine_chisel_and_clean_cache(self, docker_container: str) -> dict:
        """Ensure Chisel code is pristine and clean build cache"""
        try:
            import subprocess

            print('🔄 [BASELINE] Ensuring Chisel code is pristine and cleaning build cache...')

            # Step 1: Restore any modified Chisel files using git checkout
            restore_cmd = [
                'docker',
                'exec',
                docker_container,
                'bash',
                '-c',
                'cd /code/workspace/repo && git checkout -- . 2>/dev/null || true',
            ]
            subprocess.run(restore_cmd, capture_output=True, text=True)
            print('✅ [BASELINE] Chisel code restored to pristine state')

            # Step 2: Clean SBT build cache
            clean_cmd = ['docker', 'exec', docker_container, 'bash', '-l', '-c', 'cd /code/workspace/repo && sbt clean']
            # print('🧹 [BASELINE] Cleaning SBT build cache...')
            clean_result = subprocess.run(clean_cmd, capture_output=True, text=True, timeout=60)

            if clean_result.returncode == 0:
                pass  # SBT build cache cleaned
            else:
                pass  # SBT clean had issues

            # Step 3: Remove target directories and compilation caches
            cleanup_cmd = [
                'docker',
                'exec',
                docker_container,
                'bash',
                '-c',
                'cd /code/workspace/repo && rm -rf target/ project/target/ build/ .bloop/ .metals/ || true',
            ]
            print('🗑️ [BASELINE] Removing target directories and compilation caches...')
            subprocess.run(cleanup_cmd, capture_output=True, text=True)
            print('✅ [BASELINE] Removed compilation artifacts')

            # Step 4: Remove any existing golden directory to prevent conflicts
            rm_golden_cmd = ['docker', 'exec', docker_container, 'rm', '-rf', '/code/workspace/repo/lec_golden']
            subprocess.run(rm_golden_cmd, capture_output=True, text=True)
            print('✅ [BASELINE] Removed any existing golden directory')

            # Step 5: Clean all build directories
            build_cleanup_cmd = ['docker', 'exec', docker_container, 'bash', '-c', 'cd /code/workspace && rm -rf build/* || true']
            subprocess.run(build_cleanup_cmd, capture_output=True, text=True)
            print('✅ [BASELINE] Cleaned all build directories for fresh generation')

            return {'success': True}

        except Exception as e:
            error_msg = f'Failed to ensure pristine state: {str(e)}'
            print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _generate_fresh_baseline_verilog(self, docker_container: str) -> dict:
        """Generate fresh baseline Verilog from pristine Chisel code"""
        try:
            print('🏭 [BASELINE] Generating fresh baseline Verilog from pristine Chisel...')

            print('🔧 [BASELINE] Running: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')
            exit_code, stdout, stderr = self.builder.run_cmd(
                'bash -l -c \'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"\''
            )

            if exit_code == 0:
                print('✅ [BASELINE] Fresh baseline Verilog generated successfully')
                print('     Command used: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')

                # Create target directory and copy generated files from build_singlecyclecpu_d to build_singlecyclecpu_nd
                # so they're available in the location the backup method expects
                self.builder.run_cmd('mkdir -p /code/workspace/build/build_singlecyclecpu_nd')

                copy_exit_code, copy_stdout, copy_stderr = self.builder.run_cmd(
                    'cp -r /code/workspace/build/build_singlecyclecpu_d/* /code/workspace/build/build_singlecyclecpu_nd/'
                )

                if copy_exit_code == 0:
                    print('✅ [BASELINE] Copied baseline files to expected location')
                else:
                    print(f'⚠️  [BASELINE] Copy had issues: {copy_stderr}')

                # DEBUG: Check what opcode is actually in the generated baseline
                debug_exit_code, debug_stdout, debug_stderr = self.builder.run_cmd(
                    'grep -n _signals_T_132 /code/workspace/build/build_singlecyclecpu_nd/Control.sv'
                )
                if debug_exit_code == 0:
                    print(f'🔍 [BASELINE] Baseline contains: {debug_stdout.strip()}')
                else:
                    print(f'🔍 [BASELINE] Could not find _signals_T_132 in baseline: {debug_stderr}')

                return {'success': True}

            else:
                error_msg = f'Fresh baseline Verilog generation failed: {stderr}'
                print(f'❌ [BASELINE] {error_msg}')
                return {'success': False, 'error': error_msg}

        except Exception as e:
            error_msg = f'Fresh baseline generation failed: {str(e)}'
            print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _fix_diff_filename_case(self, verilog_diff: str, runner) -> str:
        """Fix filename case in diff to match actual files in container"""

        # Find all filenames mentioned in the diff (lines starting with --- or +++)
        filename_pattern = r'^(---|\+\+\+)\s+([^\t\n]+)'
        lines = verilog_diff.split('\n')
        corrected_lines = []

        for line in lines:
            match = re.match(filename_pattern, line)
            if match:
                prefix = match.group(1)
                filename = match.group(2).strip()

                # Extract just the filename without path
                if '/' in filename:
                    path_parts = filename.split('/')
                    base_filename = path_parts[-1]
                    dir_path = '/'.join(path_parts[:-1])
                else:
                    base_filename = filename
                    dir_path = ''

                # Find the actual case-sensitive filename in container
                try:
                    # Search for files with similar name (case-insensitive)
                    find_cmd = f'find /code/workspace -iname "{base_filename}" -type f'
                    exit_code, stdout, stderr = runner.run_cmd(find_cmd)

                    if exit_code == 0 and stdout.strip():
                        actual_files = [f.strip() for f in stdout.strip().split('\n') if f.strip()]
                        if actual_files:
                            # Use the first match and extract just the filename
                            actual_path = actual_files[0]
                            actual_filename = actual_path.split('/')[-1]

                            # Reconstruct the path with correct filename
                            if dir_path:
                                corrected_filename = f'{dir_path}/{actual_filename}'
                            else:
                                corrected_filename = actual_filename

                            corrected_line = f'{prefix} {corrected_filename}'
                            corrected_lines.append(corrected_line)
                            continue
                except Exception:
                    pass  # If search fails, use original line

            corrected_lines.append(line)

        return '\n'.join(corrected_lines)

    def _run_lec(self, docker_container: str, target_file: str) -> dict:
        """Run Logic Equivalence Check comparing LLM-fixed file vs golden design (both should have verilog_diff applied)"""
        try:
            print(f'🔍 [LEC] Running Logic Equivalence Check for target file: {target_file}')
            print(
                '🔍 [LEC] CORRECT APPROACH: comparing LLM-fixed file vs golden design (both should match buggy baseline + verilog_diff)'
            )

            # Step 1: Define paths correctly
            gate_file = f'/code/workspace/build/build_singlecyclecpu_d/{target_file}'  # LLM-fixed design
            golden_file = f'/code/workspace/repo/lec_golden/{target_file}'  # Golden design (baseline + verilog_diff)

            print(f'🔍 [LEC] Gate file (LLM-fixed): {gate_file}')
            print(f'🔍 [LEC] Golden file (baseline + verilog_diff): {golden_file}')

            # Step 2: Check if golden file exists (should be created by _create_golden_design)
            golden_check = self.builder.run_cmd(f'ls -la {golden_file}')
            if golden_check[0] != 0:
                return {
                    'success': False,
                    'error': f'Golden file not found: {golden_file} - golden design creation may have failed',
                }

            print(f'✅ [LEC] Using golden file: {golden_file}')

            # Step 4: Check if gate file exists (should be the newly compiled Verilog)
            gate_check = self.builder.run_cmd(f'ls -la {gate_file}')
            if gate_check[0] != 0:
                return {'success': False, 'error': f'Gate file not found: {gate_file}'}

            # Use Equiv_check like test_v2chisel_batch3 does
            from hagent.tool.equiv_check import Equiv_check

            checker = Equiv_check()
            if not checker.setup():
                return {'success': False, 'error': f'Equiv_check setup failed: {checker.get_error()}'}

            # Read both files using Builder filesystem API
            print('🔍 [LEC] Reading files for comparison...')
            print(f'     📖 Golden file: {golden_file}')
            print(f'     📖 Gate file: {gate_file}')

            golden_content = self.builder.filesystem.read_file(golden_file)
            gate_content = self.builder.filesystem.read_file(gate_file)

            # Show key lines from each file
            golden_lines = golden_content.split('\n')
            gate_lines = gate_content.split('\n')
            print('📊 [LEC] File comparison preview:')
            print(f'     🥇 Golden: {len(golden_lines)} lines, {len(golden_content)} chars')
            print(f'     🚪 Gate: {len(gate_lines)} lines, {len(gate_content)} chars')

            # Show line 27 (the critical line mentioned in logs)
            if len(golden_lines) >= 27:
                print(f'     🔍 Golden line 27: {golden_lines[26]}')
            if len(gate_lines) >= 27:
                print(f'     🔍 Gate line 27: {gate_lines[26]}')

            # Run equivalence check (single comparison like test_v2chisel_batch3)
            print(f'🔍 [LEC] Comparing {target_file}...')
            result = checker.check_equivalence(golden_content, gate_content)

            if result is True:
                print(f'🎉 [LEC] SUCCESS: {target_file} files are equivalent!')
                return {
                    'success': True,
                    'lec_passed': True,
                    'target_file': target_file,
                    'golden_file': golden_file,
                    'gate_file': gate_file,
                    'lec_method': 'equiv_check_direct',
                }
            elif result is False:
                print(f'❌ [LEC] FAILED: {target_file} files are NOT equivalent')

                # Show debug info for non-equivalent files (like original)
                print(f'🔍 [DEBUG] Checking content differences in {target_file}:')
                golden_lines = golden_content.split('\n')
                gate_lines = gate_content.split('\n')
                for i, (g_line, t_line) in enumerate(zip(golden_lines, gate_lines)):
                    if "7'h3" in g_line and 'signals_T_132' in g_line:
                        print(f'       Golden Line {i + 1}: {g_line.strip()}')
                    if "7'h3" in t_line and 'signals_T_132' in t_line:
                        print(f'       Gate Line {i + 1}: {t_line.strip()}')

                return {
                    'success': True,  # Pipeline continues, but LEC failed
                    'lec_passed': False,
                    'target_file': target_file,
                    'golden_file': golden_file,
                    'gate_file': gate_file,
                    'lec_method': 'equiv_check_direct',
                }
            else:
                print(f'⚠️  [LEC] INCONCLUSIVE: {target_file} equivalence check was inconclusive')
                return {
                    'success': True,  # Pipeline continues, but LEC inconclusive
                    'lec_passed': False,
                    'target_file': target_file,
                    'golden_file': golden_file,
                    'gate_file': gate_file,
                    'lec_method': 'equiv_check_direct',
                    'error': 'Equivalence check inconclusive',
                }

        except Exception as e:
            error_msg = f'LEC failed: {str(e)}'
            print(f'❌ [LEC] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _verify_module_names_consistency(
        self, docker_container: str, original_verilog_content: str, regenerated_verilog_path: str
    ) -> dict:
        """Verify that module names match between original and regenerated Verilog"""
        print('🔍 [MODULE_CHECK] Verifying module name consistency...')

        try:
            import subprocess
            import re

            # Extract module name from original Verilog
            original_module_pattern = r'module\s+(\w+)\s*[\(;]'
            original_matches = re.findall(original_module_pattern, original_verilog_content)

            if not original_matches:
                return {'success': False, 'error': 'Could not find module name in original Verilog'}

            original_module = original_matches[0]
            print(f'     📋 Original module name: {original_module}')

            # Read regenerated Verilog from Docker
            read_cmd = ['docker', 'exec', docker_container, 'cat', regenerated_verilog_path]
            read_result = subprocess.run(read_cmd, capture_output=True, text=True)

            if read_result.returncode != 0:
                return {'success': False, 'error': f'Could not read regenerated Verilog: {read_result.stderr}'}

            regenerated_content = read_result.stdout
            regenerated_matches = re.findall(original_module_pattern, regenerated_content)

            if not regenerated_matches:
                return {'success': False, 'error': 'Could not find module name in regenerated Verilog'}

            regenerated_module = regenerated_matches[0]
            print(f'     📋 Regenerated module name: {regenerated_module}')

            if original_module == regenerated_module:
                print('✅ [MODULE_CHECK] Module names match')
                return {
                    'success': True,
                    'original_module': original_module,
                    'regenerated_module': regenerated_module,
                    'match': True,
                }
            else:
                print('⚠️  [MODULE_CHECK] Module names do not match')
                return {
                    'success': True,
                    'original_module': original_module,
                    'regenerated_module': regenerated_module,
                    'match': False,
                }

        except Exception as e:
            return {'success': False, 'error': f'Module name verification error: {str(e)}'}

    def _ensure_sbt_symlink(self, docker_container: str):
        """Replace broken wrapper script with working SBT binary"""
        try:
            import subprocess

            # Remove broken wrapper script and replace with symlink
            fix_cmd = [
                'docker',
                'exec',
                '-u',
                'root',
                docker_container,
                'bash',
                '-c',
                'rm -f /root/.local/share/coursier/bin/sbt && ln -sf /root/.cache/coursier/arc/https/github.com/sbt/sbt/releases/download/v1.11.5/sbt-1.11.5.zip/sbt/bin/sbt /root/.local/share/coursier/bin/sbt',
            ]
            subprocess.run(fix_cmd, capture_output=True, text=True)
        except Exception:
            pass  # Ignore symlink errors

    def _compile_xiangshan(self, docker_container: str, force_compile: bool = True) -> dict:
        """Compile Chisel code in Docker container with enhanced verification using Runner"""
        print('🏗️  [COMPILE] Starting compilation with permission fixes...')

        try:
            # Step 1: Fix permissions on the repo directory
            print('🔧 [COMPILE] Fixing file permissions in container...')
            exit_code, stdout, stderr = self.builder.run_cmd('chown -R root:root /code/workspace/repo')
            if exit_code == 0:
                print('✅ [COMPILE] Fixed repository permissions')
            else:
                print(f'⚠️  [COMPILE] Permission fix warning: {stderr}')

            # Step 2: Clean any existing target directories that might have wrong permissions
            self.builder.run_cmd('rm -rf /code/workspace/repo/target /code/workspace/repo/project/target || true')
            print('🗑️ [COMPILE] Cleaned old target directories')

            # Step 3: Install SBT and try compilation
            print('📝 [COMPILE] Installing/ensuring SBT is available...')
            self.builder.run_cmd(
                'curl -fL https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz | gzip -d > /usr/local/bin/cs && chmod +x /usr/local/bin/cs'
            )
            self.builder.run_cmd('/usr/local/bin/cs install sbt')

            # Verify SBT is now available
            exit_code, sbt_location, stderr = self.builder.run_cmd('which sbt')
            print(f'SBT location: {sbt_location.strip()}')

            print('📝 [COMPILE] Running: sbt compile (via Runner with fixed permissions)')
            exit_code, stdout, stderr = self.builder.run_cmd("bash -l -c 'cd /code/workspace/repo && sbt compile'")

            if exit_code == 0:
                print('✅ [COMPILE] SBT compilation successful')
                return {'success': True, 'output': stdout, 'compilation_method': 'sbt_with_runner_and_permissions'}
            else:
                # SBT failed - check if it's a real compilation error vs build system issue
                sbt_error = stderr + stdout  # Combine both outputs
                if (
                    'expected class or object definition' in sbt_error
                    or 'Compilation failed' in sbt_error
                    or 'errors found' in sbt_error
                ):
                    # This is a real Scala compilation error - return it immediately
                    print('❌ [COMPILE] Real SBT compilation error detected - returning detailed error')
                    return {
                        'success': False,
                        'error': f'SBT compilation failed:\n{sbt_error}',
                        'compilation_method': 'sbt_detailed_error',
                    }
                else:
                    # This might be a build system issue - try fallbacks
                    print(f'     ⚠️  SBT compilation failed: {stderr[:200]}...')

            # Method 2: Try mill as fallback
            print('     📝 Trying Mill fallback via Runner...')
            mill_exit_code, mill_stdout, mill_stderr = self.builder.run_cmd(
                'bash -c "cd /code/workspace/repo && ./mill clean && ./mill root.compile"'
            )

            if mill_exit_code == 0:
                print('✅ [COMPILE] Compilation successful using mill')
                return {'success': True, 'output': mill_stdout, 'compilation_method': 'mill'}
            else:
                print(f'     ⚠️  Mill compilation also failed: {mill_stderr[:200]}...')

            # Both failed
            print('❌ [COMPILE] Both sbt and mill compilation failed')
            return {
                'success': False,
                'error': f'SBT failed: {stderr}\nMill failed: {mill_stderr}',
                'stdout': f'SBT stdout: {stdout}\nMill stdout: {mill_stdout}',
                'compilation_method': 'both_failed',
            }

        except Exception as e:
            error_msg = f'Compilation error: {str(e)}'
            print(f'❌ [COMPILE] {error_msg}')
            return {'success': False, 'error': error_msg, 'compilation_method': 'exception'}

    def _run_lec_check(
        self, docker_container: str, original_verilog_content: str, module_name: str, regenerated_verilog_path: str = None
    ) -> dict:
        """Run Logical Equivalence Check between original and regenerated Verilog with module name verification"""
        print('🔍 [LEC] Starting Logical Equivalence Check with module verification...')

        try:
            import subprocess

            # If regenerated Verilog path not provided, try to find it
            if not regenerated_verilog_path:
                # Find the regenerated Verilog file
                find_cmd = [
                    'docker',
                    'exec',
                    docker_container,
                    'find',
                    '/code/workspace',
                    '-name',
                    f'{module_name}.sv',
                    '-type',
                    'f',
                ]
                find_result = subprocess.run(find_cmd, capture_output=True, text=True)

                if find_result.returncode != 0 or not find_result.stdout.strip():
                    return {'success': False, 'error': f'Could not find regenerated {module_name}.sv'}

                # Use the first found file
                regenerated_verilog_path = find_result.stdout.strip().split('\n')[0]

            # Verify module name consistency before running LEC
            module_check_result = self._verify_module_names_consistency(
                docker_container, original_verilog_content, regenerated_verilog_path
            )

            if not module_check_result['success']:
                return {'success': False, 'error': f'Module verification failed: {module_check_result["error"]}'}

            if not module_check_result['match']:
                warning_msg = (
                    f'Module name mismatch: original="{module_check_result["original_module"]}" '
                    f'vs regenerated="{module_check_result["regenerated_module"]}"'
                )
                print(f'     ⚠️  [LEC] {warning_msg}')
                # Continue with LEC using the original module name for compatibility
                lec_module_name = module_check_result['original_module']
            else:
                lec_module_name = module_name

            # Read regenerated Verilog from container
            read_cmd = ['docker', 'exec', docker_container, 'cat', regenerated_verilog_path]
            read_result = subprocess.run(read_cmd, capture_output=True, text=True)

            if read_result.returncode != 0:
                return {'success': False, 'error': f'Failed to read regenerated Verilog: {read_result.stderr}'}

            new_verilog = read_result.stdout

            # Setup and run equivalence check
            print('     🔍 Running equivalence check...')
            equiv_checker = Equiv_check()

            if not equiv_checker.setup():
                return {'success': False, 'error': f'LEC setup failed: {equiv_checker.get_error()}'}

            # Run the equivalence check with verified module name
            result = equiv_checker.check_equivalence(
                gold_code=original_verilog_content, gate_code=new_verilog, desired_top=lec_module_name
            )

            lec_result = {
                'module_check': module_check_result,
                'lec_module_name': lec_module_name,
                'regenerated_verilog_path': regenerated_verilog_path,
            }

            if result is True:
                print('✅ [LEC] Designs are logically equivalent')
                lec_result.update({'success': True, 'equivalent': True, 'message': 'Designs are logically equivalent'})
                return lec_result
            elif result is False:
                counterexample = equiv_checker.get_counterexample()
                print('❌ [LEC] Designs are NOT equivalent')
                if counterexample:
                    print(f'     📋 Counterexample: {counterexample[:200]}...')
                lec_result.update(
                    {
                        'success': True,
                        'equivalent': False,
                        'message': 'Designs are not equivalent',
                        'counterexample': counterexample,
                    }
                )
                return lec_result
            else:  # result is None
                error_msg = equiv_checker.get_error()
                print('⚠️  [LEC] Equivalence check inconclusive')
                lec_result.update({'success': True, 'equivalent': None, 'message': f'Inconclusive: {error_msg}'})
                return lec_result

        except subprocess.TimeoutExpired:
            return {'success': False, 'error': 'LEC timeout'}
        except Exception as e:
            return {'success': False, 'error': f'LEC error: {str(e)}'}

    def _retry_llm_with_error(
        self,
        verilog_diff: str,
        chisel_hints: str,
        previous_chisel_diff: str,
        error_message: str,
        attempt: int,
        previous_attempts: list = None,
    ) -> dict:
        """Retry LLM call with error feedback"""
        # print(f'🔄 [LLM] Retrying with error feedback (attempt {attempt})...')

        # Format previous attempts for context
        if previous_attempts is None:
            previous_attempts = []

        attempts_context = ''
        if previous_attempts:
            attempts_context = 'Previous failed attempts:\n'
            for i, prev_attempt in enumerate(previous_attempts, 1):
                attempts_context += f'Attempt {i}: {prev_attempt["diff"]} -> Error: {prev_attempt["error"]}\n'
            attempts_context += f'\nThis is attempt {attempt}. Please generate a DIFFERENT approach.\n'

        # Use the compile_error prompt template for retry
        template_data = {
            'verilog_diff': verilog_diff,
            'chisel_hints': chisel_hints,
            'previous_chisel_diff': previous_chisel_diff,
            'compile_error': error_message,
            'previous_attempts': attempts_context,
        }

        try:
            prompt_key = 'prompt_compile_error'

            # Get the prompt configuration (same pattern as _call_llm_for_chisel_diff)
            full_config = self.template_config.template_dict.get('v2chisel_batch', {})
            if prompt_key not in full_config:
                return {'success': False, 'error': f'Prompt {prompt_key} not found in config'}

            prompt_section = full_config[prompt_key]
            prompt_template = LLM_template(prompt_section)

            # Update LLM wrapper with new template
            self.lw.chat_template = prompt_template
            self.lw.name = f'v2chisel_batch_retry_attempt_{attempt}'

            # print(f'     🎯 Using prompt: {prompt_key}')
            # print(f'     📝 Template data keys: {list(template_data.keys())}')

            # Call LLM
            response_list = self.lw.inference(template_data, prompt_index=prompt_key, n=1)

            # Check for LLM errors first
            if self.lw.last_error:
                return {'success': False, 'error': f'LLM error: {self.lw.last_error}'}

            if not response_list or not response_list[0].strip():
                return {'success': False, 'error': 'LLM returned empty response'}

            generated_diff = response_list[0].strip()

            if generated_diff is None:
                return {'success': False, 'error': 'LLM returned None'}

            # Clean up the generated diff
            if '```' in generated_diff:
                lines = generated_diff.split('\n')
                cleaned_lines = []
                in_code_block = False

                for line in lines:
                    if line.strip().startswith('```'):
                        in_code_block = not in_code_block
                        continue
                    if in_code_block or not line.strip().startswith('```'):
                        cleaned_lines.append(line)

                generated_diff = '\n'.join(cleaned_lines).strip()

            print(f'     ✅ LLM retry generated diff: {len(generated_diff)} characters')
            return {'success': True, 'chisel_diff': generated_diff, 'prompt_used': prompt_key, 'attempt': attempt}

        except Exception as e:
            print(f'     ❌ LLM retry failed: {e}')
            return {'success': False, 'error': str(e)}

    def _process_single_bug(
        self, bug_idx: int, bug_entry: dict, local_files: list, docker_container: str, docker_patterns: list
    ) -> dict:
        """Process a single bug entry with module_finder"""

        # Initialize golden design success to False
        golden_design_success = False

        # Create BugInfo object to handle bug data extraction
        bug_info = BugInfo(bug_entry, bug_idx)

        # Print debug information (matches original output exactly)
        bug_info.print_debug_info()

        # Extract variables for backwards compatibility with existing code
        file_name = bug_info.file_name
        unified_diff = bug_info.unified_diff
        module_name = bug_info.module_name

        # print(f'Processing module: {module_name}')
        # print(f'Docker container: {docker_container}')

        # OPTIMIZATION: Search Docker files specific to this module
        # print(f'🐳 Searching Docker for module: {module_name}')
        docker_files = self._find_chisel_files_docker_filtered(docker_container, docker_patterns, module_name)

        # Combine local and filtered Docker files
        all_files = local_files + docker_files
        # print(f'📁 Total files for this bug: {len(all_files)} (local: {len(local_files)}, docker: {len(docker_files)})')

        # Search for actual Verilog files in Docker to improve module context
        verilog_context = self._find_verilog_files_in_docker(docker_container, module_name)

        # Step 4: Use HintsGenerator to find hints
        print('✅ Step 4: Hint Generation - START')
        hints_result = self.hints_generator.find_hints(bug_info, all_files, docker_container)

        # Extract results for backwards compatibility
        final_hints = hints_result['hints']
        hints_source = hints_result['source']
        hits = hints_result.get('hits', [])

        # Print hint files and paths (matches original output format)
        if hints_source == 'module_finder' and hits:
            print('Hint files:')
            for i, hit in enumerate(hits[:5]):  # Show first 5 hits
                if hit.file_name.startswith('docker:'):
                    file_path = hit.file_name.split(':', 2)[2]
                    print(f'  [{i + 1}] {file_path} (lines {hit.start_line}-{hit.end_line}, confidence: {hit.confidence:.2f})')
                else:
                    print(
                        f'  [{i + 1}] {hit.file_name} (lines {hit.start_line}-{hit.end_line}, confidence: {hit.confidence:.2f})'
                    )

        # print(f'📝 Final hints source: {hints_source}')

        # STEP 3: Create MASTER backup before starting any LLM attempts
        print('✅ Step 5: Master Backup - START')
        # print('💾 [MASTER_BACKUP] Creating master backup of original files before LLM processing...')
        master_backup_info = self._create_master_backup(docker_container, unified_diff)
        if not master_backup_info['success']:
            print(f'❌ MASTER_BACKUP: Failed - {master_backup_info.get("error", "Unknown error")}')
            print('     ⚠️  Continuing without backup (risky!)')

        # STEP 4: LLM + Applier + Compiler retry loop WITH ORIGINAL RESTORE
        llm_result = {}
        applier_result = {}
        compile_result = {}
        generated_chisel_diff = ''
        max_retries = 3
        current_attempt = 1
        previous_attempts = []  # Track previous failed attempts for LLM context

        print(f'🔧 [DEBUG] Final hints length: {len(final_hints)} characters')
        print(f'🔧 [DEBUG] Final hints (first 200 chars): {final_hints[:200]}...')

        if final_hints.strip():
            print('🤖 [LLM] Starting LLM call for Chisel diff generation...')

            # DEBUG: Print the exact query being sent to LLM
            # print('🔍 [DEBUG] VERILOG_DIFF being sent to LLM:')
            # print('-' * 40)
            # print(unified_diff)
            # print('-' * 40)
            #
            # print('🔍 [DEBUG] CHISEL_HINTS being sent to LLM:')
            # print('=' * 80)
            # print(final_hints)  # Comment out hints printing
            # print('=' * 80)
            # print(f'🔍 [DEBUG] CHISEL_HINTS length: {len(final_hints)} characters')

            print('🔧 [DEBUG] About to call _call_llm_for_chisel_diff with:')
            print(f'     verilog_diff length: {len(unified_diff)}')
            print(f'     chisel_hints length: {len(final_hints)}')
            print(f'     attempt: {current_attempt}')

            llm_result = self._call_llm_for_chisel_diff(
                verilog_diff=unified_diff, chisel_hints=final_hints, attempt=current_attempt
            )

            print(f'🔧 [DEBUG] _call_llm_for_chisel_diff returned: {llm_result}')

            # Retry loop for LLM + Applier + Compiler
            while current_attempt <= max_retries:
                if not llm_result['success']:
                    print(f'❌ [LLM] Failed to generate Chisel diff: {llm_result.get("error", "Unknown error")}')
                    break

                generated_chisel_diff = llm_result['chisel_diff']
                print(f'LLM Generated Chisel Diff (attempt {current_attempt}):')
                print('=' * 50)
                print(generated_chisel_diff)
                print('=' * 50)

                # STEP 1: Apply the diff directly (we have master backup as safety net)
                print('✅ Step 6: Diff Application - START')
                applier_result = self._apply_chisel_diff(generated_chisel_diff, docker_container)

                if applier_result['success']:
                    print('✅ APPLIER: Successfully applied diff')

                    # STEP 3: Try to compile
                    print('✅ Step 7: Compilation - START')
                    compile_result = self._compile_xiangshan(docker_container)

                    if compile_result['success']:
                        print('✅ COMPILATION: Success')

                        # STEP 4: Try to generate Verilog from compiled Chisel
                        print('✅ Step 8: Verilog Generation - START')
                        verilog_gen_result = self._generate_verilog_from_chisel(docker_container, module_name)

                        if verilog_gen_result['success']:
                            print('✅ VERILOG_GENERATION: Success')

                            # SUCCESS: Basic pipeline completed successfully (compilation + verilog generation)
                            # Clean up MASTER backup since core functionality worked
                            self._cleanup_master_backup(docker_container, master_backup_info)
                            print('✅ PIPELINE: Basic pipeline successful - compilation and verilog generation completed!')
                            break
                        else:
                            verilog_error = verilog_gen_result.get('error', 'Unknown error')
                            is_tooling_issue = verilog_gen_result.get('tooling_issue', False)

                            print(f'❌ VERILOG_GENERATION: Failed - {verilog_error}')

                            # RESTORE: Verilog generation failed, restore to ORIGINAL state
                            restore_result = self._restore_to_original(
                                docker_container, master_backup_info, 'verilog_generation_failure'
                            )

                            if is_tooling_issue:
                                print('⚠️  This appears to be a tooling/configuration issue, not a Chisel diff problem')
                                print('   Skipping LLM retry as the issue is not related to the generated diff')
                                print('   Suggestions:')
                                print('   - Ensure Main object exists with ChiselStage.emitSystemVerilogFile')
                                print('   - Check mill/sbt configuration')
                                print('   - Verify build dependencies')
                                compile_result = {
                                    'success': False,
                                    'error': f'Tooling issue: {verilog_error}',
                                    'compilation_method': 'verilog_gen_tooling_failure',
                                }
                                break
                            else:
                                # This might be related to the Chisel diff - retry with LLM
                                full_error_msg = f'Compilation succeeded but Verilog generation failed: {verilog_error}'
                                if current_attempt < max_retries:
                                    # Record this failed attempt
                                    previous_attempts.append({'diff': generated_chisel_diff, 'error': full_error_msg})

                                    print(
                                        f'🔄 RETRY: Attempting retry {current_attempt + 1}/{max_retries} with Verilog generation error'
                                    )
                                    llm_result = self._retry_llm_with_error(
                                        verilog_diff=unified_diff,
                                        chisel_hints=final_hints,
                                        previous_chisel_diff=generated_chisel_diff,
                                        error_message=full_error_msg,
                                        attempt=current_attempt + 1,
                                        previous_attempts=previous_attempts,
                                    )
                                    current_attempt += 1
                                else:
                                    print(f'❌ [FINAL] Maximum retries ({max_retries}) reached')
                                    break
                    else:
                        # Compilation failed - restore backup and retry with compilation error feedback
                        compile_error_msg = compile_result.get('error', 'Unknown compilation error')
                        print(f'❌ COMPILATION: Failed - {compile_error_msg}')

                        # DEBUG: Print detailed compilation error
                        print('🔍 [DEBUG] Full compilation error details:')
                        print('=' * 60)
                        print(compile_error_msg)
                        print('=' * 60)

                        # RESTORE: Compilation failed, restore to ORIGINAL state before retry
                        restore_result = self._restore_to_original(docker_container, master_backup_info, 'compilation_failure')

                        if current_attempt < max_retries:
                            # Record this failed attempt
                            previous_attempts.append({'diff': generated_chisel_diff, 'error': compile_error_msg})

                            print(f'🔄 RETRY: Attempting retry {current_attempt + 1}/{max_retries} with compilation error')
                            llm_result = self._retry_llm_with_error(
                                verilog_diff=unified_diff,
                                chisel_hints=final_hints,
                                previous_chisel_diff=generated_chisel_diff,
                                error_message=compile_error_msg,
                                attempt=current_attempt + 1,
                                previous_attempts=previous_attempts,
                            )
                            current_attempt += 1
                        else:
                            print(f'❌ [FINAL] Maximum retries ({max_retries}) reached')
                            break
                else:
                    # Applier failed - MUST restore since diff might have been partially applied
                    error_msg = applier_result.get('error', 'Unknown error')
                    print(f'❌ APPLIER: Failed - {error_msg}')

                    # RESTORE: Applier failed, restore to ORIGINAL state before retry
                    restore_result = self._restore_to_original(docker_container, master_backup_info, 'applier_failure')

                    # Don't retry LLM for permission/file writing errors
                    if 'Permission denied' in error_msg or 'docker cp' in error_msg or 'chmod' in error_msg:
                        print('⚠️ This is a Docker permission issue, not an LLM diff problem. Skipping LLM retry.')
                        break

                    if current_attempt < max_retries:
                        # Record this failed attempt
                        previous_attempts.append({'diff': generated_chisel_diff, 'error': error_msg})

                        print(f'🔄 RETRY: Attempting retry {current_attempt + 1}/{max_retries}')
                        llm_result = self._retry_llm_with_error(
                            verilog_diff=unified_diff,
                            chisel_hints=final_hints,
                            previous_chisel_diff=generated_chisel_diff,
                            error_message=error_msg,
                            attempt=current_attempt + 1,
                            previous_attempts=previous_attempts,
                        )
                        current_attempt += 1
                    else:
                        print(f'❌ [FINAL] Maximum retries ({max_retries}) reached')
                        break
        else:
            print('❌ [LLM] No hints available - skipping LLM call')
            print(f'     final_hints is empty or whitespace only: "{final_hints}"')
            print('⚠️ LLM: Skipped - no hints available')
            llm_result = {'success': False, 'error': 'No hints available for LLM'}
            applier_result = {'success': False, 'error': 'No LLM output to apply'}
            compile_result = {'success': False, 'error': 'No diff applied to compile'}

        # Check if verilog_gen_result exists and was successful
        verilog_success = False
        if 'verilog_gen_result' in locals():
            verilog_success = verilog_gen_result.get('success', False)

        # RUN LEC ONCE at the end like test_v2chisel_batch3, only if basic pipeline succeeded
        lec_result = {'success': False, 'lec_passed': False, 'error': 'LEC not attempted'}
        if (
            llm_result.get('success', False)
            and applier_result.get('success', False)
            and compile_result.get('success', False)
            and verilog_success
        ):
            print('\n🎉 [LEC] Basic pipeline successful - now running final LEC check like test_v2chisel_batch3')

            # Step 2: Create golden design by applying verilog_diff to baseline before LEC
            print('✅ Step 2: Golden Design Creation - START')

            # Use GoldenDesignBuilder component for cleaner code organization
            from hagent.step.v2chisel_batch.components.golden_design_builder import GoldenDesignBuilder

            golden_builder = GoldenDesignBuilder(self.builder, debug=True)

            golden_design_result = golden_builder.create_golden_design(unified_diff, master_backup_info, docker_container)

            if golden_design_result['success']:
                print('✅ [GOLDEN] Golden design created successfully')
                golden_design_success = True
            else:
                print(f'❌ [GOLDEN] Golden design creation failed: {golden_design_result.get("error", "Unknown error")}')
                golden_design_success = False

            print('🔍 [LEC] Step: Running final equivalence check between golden and gate designs...')

            # Run LEC directly (compares golden design vs LLM-generated design)
            lec_result = self._run_lec(docker_container, file_name)

            if lec_result.get('lec_passed', False):
                print('🎉 [LEC] SUCCESS: Designs are equivalent - changes are correct!')
            else:
                lec_error = lec_result.get('error', 'Designs are NOT equivalent')
                print(f'❌ [LEC] FAILED: {lec_error}')
        else:
            print('\n⚠️  [LEC] Skipping LEC - basic pipeline did not complete successfully')
            lec_result = {'success': False, 'lec_passed': False, 'error': 'Basic pipeline incomplete'}

        # Extract LEC results for final evaluation
        lec_passed = lec_result.get('lec_passed', False)

        pipeline_fully_successful = (
            llm_result.get('success', False)
            and applier_result.get('success', False)
            and compile_result.get('success', False)
            and verilog_success
            and lec_passed  # Only consider successful if LEC confirmed designs are equivalent
        )

        print(
            f'📊 [PIPELINE_CHECK] LLM: {llm_result.get("success", False)}, Applier: {applier_result.get("success", False)}, Compile: {compile_result.get("success", False)}, Verilog: {verilog_success}, LEC_passed: {lec_passed}'
        )

        if not pipeline_fully_successful and master_backup_info.get('success', False):
            print(
                '🔄 [FINAL_RESTORE] Pipeline not fully successful OR LEC did not confirm equivalence - restoring to original state'
            )
            print(f'     Reason: Full pipeline success (including LEC pass) = {pipeline_fully_successful}')
            final_restore_result = self._restore_to_original(
                docker_container, master_backup_info, 'pipeline_incomplete_or_failed'
            )
            # Keep master backup for potential future runs - don't clean up yet
        else:
            print('✅ [FINAL_CHECK] Pipeline fully successful AND LEC confirmed equivalence - keeping changes permanent')
            final_restore_result = {'success': True, 'message': 'No restore needed'}

        # Return results for this bug
        result = {
            'bug_index': bug_idx,
            'verilog_file': file_name,
            'module_name': module_name,
            'unified_diff': unified_diff,
            'module_finder_hits': len(hits),
            'hits': [
                {
                    'module_name': hit.module_name,
                    'file_name': hit.file_name,
                    'start_line': hit.start_line,
                    'end_line': hit.end_line,
                    'confidence': hit.confidence,
                }
                for hit in hits
            ]
            if hits
            else [],
            'hints_source': hints_source,
            'final_hints': final_hints,
            'has_hints': bool(final_hints.strip()),
            'llm_success': llm_result.get('success', False),
            'generated_chisel_diff': generated_chisel_diff,
            'llm_prompt_used': llm_result.get('prompt_used', ''),
            'llm_error': llm_result.get('error', '') if not llm_result.get('success', False) else '',
            'applier_success': applier_result.get('success', False),
            'applier_error': applier_result.get('error', '') if not applier_result.get('success', False) else '',
            'compile_success': compile_result.get('success', False),
            'compile_error': compile_result.get('error', '') if not compile_result.get('success', False) else '',
            'compile_method': compile_result.get('compilation_method', ''),
            'verilog_generation_attempted': 'verilog_gen_result' in locals() and current_attempt <= max_retries,
            'verilog_generation_success': locals().get('verilog_gen_result', {}).get('success', False),
            'verilog_generation_error': locals().get('verilog_gen_result', {}).get('error', ''),
            'lec_attempted': lec_result.get('success', False) or 'error' in lec_result,
            'lec_equivalent': lec_result.get('lec_passed', None),
            'lec_error': lec_result.get('error', ''),
            'master_backup_created': master_backup_info.get('success', False),
            'master_backup_id': master_backup_info.get('backup_id', ''),
            'files_backed_up': len(master_backup_info.get('files_backed_up', [])),
            'restore_to_original_performed': locals().get('restore_result', {}).get('success', False)
            or locals().get('final_restore_result', {}).get('success', False),
            'restore_reason': locals().get('restore_result', {}).get('restore_reason', '')
            or locals().get('final_restore_result', {}).get('restore_reason', ''),
            'total_attempts': current_attempt,
            'pipeline_success': (
                llm_result.get('success', False)
                and applier_result.get('success', False)
                and compile_result.get('success', False)
                and locals().get('verilog_gen_result', {}).get('success', False)
            ),
            'golden_design_success': locals().get('golden_design_success', False),
            'lec_success': locals().get('lec_result', {}).get('success', False),
            'lec_method': locals().get('lec_result', {}).get('lec_method', 'none'),
        }

        return result

    def run(self, data):
        """Main processing function - Step 1: Read bugs and call module_finder"""
        print('\n🚀 Starting V2chisel_batch processing...')

        print('✅ Step 2: Input Processing - START')

        # Step 1: Load bug list (check input_data first, then external file)
        if 'bugs' in self.input_data:
            # Bugs defined directly in input file
            bugs = self.input_data['bugs']
            print(f'[V2chisel_batch] Using bugs from input_data: {len(bugs)} bugs')
        else:
            # Load from external bug list file
            bug_file = self.input_data.get('bug_list_file', 'bug_lists_unified.yaml')
            bugs = self._load_bug_list(bug_file)

        # Step 2: Get configuration (but don't search files yet - we'll do per-bug filtering)
        chisel_patterns = self.input_data.get('chisel_patterns', [self.chisel_source_pattern])
        # Also support single pattern for backward compatibility
        if 'chisel_pattern' in self.input_data:
            single_pattern = self.input_data['chisel_pattern']
            if isinstance(single_pattern, str):
                chisel_patterns = [single_pattern]
            else:
                chisel_patterns = single_pattern

        # Get local files once (these are small)
        print('[V2chisel_batch] Finding local Chisel files...')
        local_files = []
        for pattern in chisel_patterns:
            files = glob.glob(pattern, recursive=True)
            local_files.extend(files)
        print(f'[V2chisel_batch] Found {len(local_files)} local Chisel files')

        # Get the actual container name from Runner
        actual_container_name = None
        if self.builder and hasattr(self.builder, 'container_manager'):
            container_mgr = self.builder.container_manager
            if hasattr(container_mgr, 'container') and container_mgr.container:
                # Get container name from Docker container object
                actual_container_name = container_mgr.container.name

        if actual_container_name:
            print(f'✅ [V2chisel_batch] Using Runner container: {actual_container_name}')
            self.input_data['docker_container'] = actual_container_name
        else:
            print('⚠️  [V2chisel_batch] Could not get Runner container name, using default')

        # Step 3: Process each bug
        print(f'\n🔄 Processing {len(bugs)} bugs...')
        results = []

        docker_container = self.input_data.get('docker_container', actual_container_name or 'hagent')
        docker_patterns = self.input_data.get('docker_patterns', ['/code/workspace/repo'])

        # Step 3.1: Generate fresh baseline Verilog before processing any bugs
        print('\n🏭 [BASELINE] Preparing fresh baseline Verilog for golden design comparison...')
        pristine_result = self._ensure_pristine_chisel_and_clean_cache(docker_container)
        if not pristine_result['success']:
            print(f'❌ [BASELINE] Failed to ensure pristine state: {pristine_result.get("error", "Unknown error")}')
            print('⚠️  [BASELINE] Continuing anyway, but results may be inconsistent')

        baseline_result = self.baseline_verilog_generator.generate_fresh_baseline(docker_container)
        if not baseline_result['success']:
            print(f'❌ [BASELINE] Failed to generate fresh baseline: {baseline_result.get("error", "Unknown error")}')
            print('⚠️  [BASELINE] Continuing with existing Verilog files (may be stale)')
        else:
            print('✅ [BASELINE] Fresh baseline Verilog generation complete\n')

        for i, bug_entry in enumerate(bugs):
            try:
                bug_result = self._process_single_bug(i, bug_entry, local_files, docker_container, docker_patterns)
                results.append(bug_result)

                # Show progress based on actual pipeline success
                pipeline_success = bug_result.get('pipeline_success', False)
                if pipeline_success:
                    print(f'✅ Bug #{i + 1} completed successfully (full pipeline success)')
                else:
                    print(f'⚠️  Bug #{i + 1} processed but failed (pipeline incomplete or failed)')

                # Add small delay to see output clearly
                if self.debug:
                    import time

                    time.sleep(0.1)

            except Exception as e:
                print(f'❌ Bug #{i + 1} failed: {e}')
                # Continue with next bug
                results.append(
                    {
                        'bug_index': i,
                        'error': str(e),
                        'verilog_file': bug_entry.get('file', 'unknown'),
                        'module_finder_hits': 0,
                        'hits': [],
                    }
                )

        # Step 4: Generate summary
        total_bugs = len(results)
        bugs_with_hints = sum(1 for r in results if r.get('has_hints', False))
        module_finder_successes = sum(1 for r in results if r.get('hints_source') == 'module_finder')
        metadata_fallbacks = sum(1 for r in results if r.get('hints_source') == 'metadata_fallback')
        # no_hints = sum(1 for r in results if r.get('hints_source') == 'none')

        # Pipeline statistics (TRUE success = full pipeline completion)
        pipeline_successes = sum(1 for r in results if r.get('pipeline_success', False))
        llm_successes = sum(1 for r in results if r.get('llm_success', False))
        llm_attempts = sum(1 for r in results if r.get('has_hints', False))  # Only attempted where hints exist

        # Golden design and LEC statistics
        golden_design_successes = sum(1 for r in results if r.get('golden_design_success', False))
        lec_successes = sum(1 for r in results if r.get('lec_success', False))
        lec_attempts = sum(1 for r in results if r.get('lec_method') != 'none')

        print('\n📊 V2CHISEL_BATCH COMPLETE SUMMARY:')
        # Summary stats commented out for cleaner output
        # print(f'   📋 Total bugs processed: {total_bugs}')
        # print('   🔍 HINTS GENERATION:')
        # print(f'       Module_finder successes: {module_finder_successes}')
        # print(f'       Metadata fallbacks used: {metadata_fallbacks}')
        # print(f'       No hints available: {no_hints}')
        # print(f'       📈 Total with hints: {bugs_with_hints}/{total_bugs} ({bugs_with_hints / total_bugs * 100:.1f}%)')
        # print('   🤖 LLM CHISEL DIFF GENERATION:')
        # print(f'       LLM attempts made: {llm_attempts}')
        # print(f'       LLM successes: {llm_successes}')
        # print(f'       📈 LLM success rate: {llm_successes / llm_attempts * 100:.1f}%' if llm_attempts > 0 else '0.0%')
        # print('   🎯 PIPELINE STATUS:')
        # print(f'       ✅ Ready for next step: {llm_successes} bugs have Chisel diffs')
        # print(f'       ⚠️  Need attention: {total_bugs - llm_successes} bugs failed LLM generation')
        print(f'Processed {total_bugs} bugs: {pipeline_successes} successful (full pipeline), {llm_successes} LLM successful')
        if lec_attempts > 0:
            print(
                f'LEC Results: {lec_successes}/{lec_attempts} successful ({lec_successes / lec_attempts * 100:.1f}%), Golden Design: {golden_design_successes}/{total_bugs} successful'
            )

        # Return results
        final_result = data.copy()
        final_result['v2chisel_batch_with_llm'] = {
            'total_bugs': total_bugs,
            'pipeline_successes': pipeline_successes,
            'pipeline_success_rate': pipeline_successes / total_bugs * 100 if total_bugs > 0 else 0.0,
            'module_finder_successes': module_finder_successes,
            'metadata_fallbacks': metadata_fallbacks,
            'bugs_with_hints': bugs_with_hints,
            'hints_coverage_rate': bugs_with_hints / total_bugs * 100,
            'llm_attempts': llm_attempts,
            'llm_successes': llm_successes,
            'llm_success_rate': llm_successes / llm_attempts * 100 if llm_attempts > 0 else 0.0,
            'golden_design_successes': golden_design_successes,
            'lec_attempts': lec_attempts,
            'lec_successes': lec_successes,
            'lec_success_rate': lec_successes / lec_attempts * 100 if lec_attempts > 0 else 0.0,
            'bug_results': results,
            'local_files_found': len(local_files),
            'chisel_patterns_used': chisel_patterns,
            'docker_container': docker_container,
            'docker_patterns': docker_patterns,
        }

        # Final cleanup
        self._cleanup_temp_files()
        self.cleanup()  # Clean up Runner resources

        return final_result


def wrap_literals(obj):
    """Wrap multi-line strings as YAML literal scalars"""
    if isinstance(obj, dict):
        return {k: wrap_literals(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [wrap_literals(elem) for elem in obj]
    elif isinstance(obj, str) and '\n' in obj:
        return LiteralScalarString(obj)
    else:
        return obj


def parse_arguments():
    parser = argparse.ArgumentParser(description='V2Chisel Batch Processing - Step 1')
    parser.add_argument('-o', required=True, help='Output YAML file')
    parser.add_argument('input_file', help='Input YAML file (can be minimal)')
    return parser.parse_args()


def main():
    """Main function - works exactly like test_v2chisel_batch command"""

    # Parse command line arguments exactly like real v2chisel_batch
    parser = argparse.ArgumentParser(
        description='V2chisel_batch with real LLM calls',
        epilog='Usage: uv run python3 v2chisel_batch.py -o output.yaml input.yaml',
    )
    parser.add_argument('input_file', help='Input YAML file (e.g., single_adder_test.yaml)')
    parser.add_argument('-o', '--output', required=True, help='Output YAML file')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')

    args = parser.parse_args()

    print('🚀 V2CHISEL_BATCH WITH REAL LLM')
    print('=' * 80)
    print('Purpose: Run complete v2chisel_batch pipeline with real LLM calls')
    print(f'Input:   {args.input_file}')
    print(f'Output:  {args.output}')
    print('=' * 80)
    print()

    # Check input file exists
    if not os.path.exists(args.input_file):
        print(f'❌ [V2chisel_batch] Input file not found: {args.input_file}')
        return 1

    # Load input data
    from ruamel.yaml import YAML

    yaml = YAML()
    yaml.preserve_quotes = True
    yaml.default_flow_style = False

    try:
        with open(args.input_file, 'r') as f:
            input_data = yaml.load(f)
        print(f'📂 [V2chisel_batch] Loaded input file: {args.input_file}')
    except Exception as e:
        print(f'❌ [V2chisel_batch] Error loading input file {args.input_file}: {e}')
        return 1

    processor = None
    try:
        # Create processor
        processor = V2chisel_batch()

        # Set required attributes for Step initialization
        processor.input_path = args.input_file
        processor.output_path = args.output

        # CRITICAL: Call set_io() and setup() to initialize all required attributes
        try:
            # Use set_io() instead of parse_arguments() for programmatic calls
            print(f'🔧 [V2chisel_batch] Setting I/O: input={args.input_file}, output={args.output}')
            processor.set_io(args.input_file, args.output)
            print('🔧 [V2chisel_batch] I/O set, now calling setup()...')
            processor.setup()
            print('✅ [V2chisel_batch] Processor setup completed successfully')
        except Exception as e:
            print(f'⚠️ [V2chisel_batch] Processor setup had issues but continuing: {e}')
            import traceback

            traceback.print_exc()
            # Manually set critical attributes as fallback
            processor.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'
            processor.debug = True
            processor.module_finder = Module_finder()  # Initialize module finder
            processor.hints_generator = HintsGenerator(
                processor.module_finder, builder=processor.builder, debug=processor.debug
            )  # Initialize hints generator
            processor.golden_design_builder = GoldenDesignBuilder(
                processor.builder, debug=processor.debug
            )  # Initialize golden design builder
            processor.baseline_verilog_generator = BaselineVerilogGenerator(
                processor.builder, debug=processor.debug
            )  # Initialize baseline verilog generator

            # Create mock template_config for LLM calls
            class MockTemplateConfig:
                def __init__(self):
                    self.template_dict = {
                        'v2chisel_batch': {
                            'llm': {'model': 'bedrock/us.meta.llama3-3-70b-instruct-v1:0', 'temperature': 0.1},
                            'prompt_initial': [
                                {
                                    'role': 'system',
                                    'content': 'You are an expert AI assistant specialized in translating Verilog changes to corresponding Chisel code modifications.',
                                },
                                {
                                    'role': 'user',
                                    'content': 'I have a Chisel hardware design that generates Verilog. I need to modify the Chisel code to match specific changes made to the Verilog.\n\nHere is the unified diff showing the desired Verilog changes:\n```\n{verilog_diff}\n```\n\nHere are hints from the corresponding Chisel code that likely need modification:\n```\n{chisel_hints}\n```\n\nPlease generate a unified diff for the Chisel code that will produce the desired Verilog changes.\n\nRequirements:\n- Output ONLY the unified diff in standard format\n- Use minimal hunks containing only the necessary changes\n- Do NOT include any explanation, commentary, or notes\n- Ensure the diff can be applied to existing Chisel source files\n\nGenerate the Chisel unified diff now:',
                                },
                            ],
                            'prompt_compile_error': [
                                {
                                    'role': 'system',
                                    'content': 'You are an AI specialized in fixing Chisel compilation errors while maintaining the intended functionality.',
                                },
                                {
                                    'role': 'user',
                                    'content': 'The previous Chisel diff caused compilation errors. I need a corrected version.\n\nOriginal Verilog diff target:\n```\n{verilog_diff}\n```\n\nPrevious Chisel diff that failed:\n```\n{previous_chisel_diff}\n```\n\nCompilation error:\n```\n{compile_error}\n```\n\nUpdated hints from Chisel code:\n```\n{chisel_hints}\n```\n\nPlease generate a corrected unified diff that:\n- Fixes the compilation error\n- Still achieves the target Verilog changes\n- Uses proper Chisel syntax\n\nOutput ONLY the corrected unified diff:',
                                },
                            ],
                            'prompt_lec_error': [
                                {
                                    'role': 'system',
                                    'content': 'You are an AI expert at ensuring Chisel-generated Verilog passes Logic Equivalence Check (LEC) against target specifications.',
                                },
                                {
                                    'role': 'user',
                                    'content': 'The Chisel code compiled successfully but failed Logic Equivalence Check (LEC). I need corrections.\n\nTarget Verilog diff:\n```\n{verilog_diff}\n```\n\nCurrent Chisel diff:\n```\n{current_chisel_diff}\n```\n\nLEC failure details:\n```\n{lec_error}\n```\n\nHints from Chisel code for potential fixes:\n```\n{chisel_hints}\n```\n\nPlease generate a refined unified diff that will pass LEC by ensuring logical equivalence with the target Verilog.\n\nOutput ONLY the refined unified diff:',
                                },
                            ],
                            'prompt_final_attempt': [
                                {
                                    'role': 'system',
                                    'content': 'You are an AI making a final attempt to generate working Chisel code. Use all available information and consider alternative approaches.',
                                },
                                {
                                    'role': 'user',
                                    'content': 'Previous attempts have failed. This is the final attempt to generate correct Chisel code.\n\nTarget Verilog changes:\n```\n{verilog_diff}\n```\n\nAll previous attempts and their errors:\n```\n{attempt_history}\n```\n\nComplete Chisel hints with broader context:\n```\n{chisel_hints}\n```\n\nPlease make a final attempt with a potentially different approach. Consider:\n- Alternative Chisel constructs that achieve the same Verilog\n- Broader context changes if needed\n- Different interpretation of the Verilog requirements\n\nOutput ONLY the unified diff for this final attempt:',
                                },
                            ],
                        }
                    }

            if not hasattr(processor, 'template_config'):
                processor.template_config = MockTemplateConfig()

            # Initialize LLM if it failed in setup
            if not hasattr(processor, 'lw'):
                try:
                    conf_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'v2chisel_batch_conf.yaml')

                    # Load template config to get default LLM settings
                    from hagent.core.llm_template import LLM_template

                    template_config = LLM_template(conf_file)

                    # Get the full v2chisel_batch configuration (includes prompts)
                    full_config = template_config.template_dict.get('v2chisel_batch', {})
                    llm_config = full_config.get('llm', {})

                    # Allow override from input_data while keeping generic structure
                    final_llm_config = {**llm_config, **input_data.get('v2chisel_batch', {}).get('llm', {})}

                    # Create complete configuration with LLM and prompts
                    complete_config = {**full_config}  # Include all prompts
                    complete_config['llm'] = final_llm_config  # Override LLM config

                    # Use same pattern as working examples - pass complete config
                    processor.lw = LLM_wrap(
                        name='v2chisel_batch',
                        log_file='v2chisel_batch.log',
                        conf_file=conf_file,
                        overwrite_conf=complete_config,
                    )

                    # Also store the template_config for consistency
                    processor.template_config = template_config

                    print('✅ [V2chisel_batch] LLM initialized in fallback')
                except Exception as llm_error:
                    print(f'❌ [V2chisel_batch] Could not initialize LLM: {llm_error}')
                    return 1

            # Set input_data to avoid None reference
            if not hasattr(processor, 'input_data'):
                processor.input_data = input_data

        print('🚀 [V2chisel_batch] STARTING COMPLETE PIPELINE')
        print('=' * 60)
        print()

        # CRITICAL: Ensure Chisel code is pristine, then generate fresh baseline
        print('✅ Step 1: Initialization & Setup - START')

        # First, make sure Chisel code is in original state and clean build cache
        # print('🔄 [V2chisel_batch] Ensuring Chisel code is pristine and cleaning build cache...')

        # Setup processor's Runner to access Docker commands
        # print('🔧 [V2chisel_batch] Setting up Docker container...')
        if not processor.builder.setup():
            print('❌ Step 1: Initialization & Setup - FAILED')
            return 1
        # print('✅ [V2chisel_batch] Docker container setup successful')

        # Install coursier and SBT
        print('📝 [V2chisel_batch] Installing/ensuring SBT is available...')
        processor.builder.run_cmd(
            'curl -fL https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz | gzip -d > /usr/local/bin/cs && chmod +x /usr/local/bin/cs'
        )
        processor.builder.run_cmd('/usr/local/bin/cs install sbt')

        # Verify SBT is now available
        sbt_check_exit, sbt_check_out, sbt_check_err = processor.builder.run_cmd('which sbt')
        print(f'SBT location: {sbt_check_out.strip()}')

        # Step 1: Fix git ownership and restore Chisel source files
        print('🔄 [V2chisel_batch] Fixing git ownership and restoring Chisel code...')
        processor.builder.run_cmd('git config --global --add safe.directory /code/workspace/repo')
        exit_code, stdout, stderr = processor.builder.run_cmd(
            'git -C /code/workspace/repo checkout HEAD -- src/main/scala/components/control.scala'
        )
        if exit_code != 0:
            print(f'⚠️  [V2chisel_batch] Could not restore Chisel to pristine state: {stderr}')
        else:
            print('✅ [V2chisel_batch] Chisel code restored to pristine state')

        # Step 2: Clean SBT build cache using the working pattern
        print('🧹 [V2chisel_batch] Cleaning SBT build cache...')
        exit_code, stdout, stderr = processor.builder.run_cmd("bash -l -c 'cd /code/workspace/repo && sbt clean'")
        if exit_code != 0:
            print(f'⚠️  [V2chisel_batch] SBT clean failed (non-critical): {stderr}')
        else:
            print('✅ [V2chisel_batch] SBT build cache cleaned')

        # Also remove target directories and .bloop cache for more aggressive cleaning
        print('🗑️ [V2chisel_batch] Removing target directories and compilation caches...')
        processor.builder.run_cmd('rm -rf target/ project/target/ .bloop/ || true', cwd='/code/workspace/repo')
        print('✅ [V2chisel_batch] Removed compilation artifacts')

        # Step 3: Remove any existing golden directory from previous runs
        processor.builder.run_cmd('rm -rf /code/workspace/repo/lec_golden')
        print('✅ [V2chisel_batch] Removed any existing golden directory')

        # Step 4: Clean both directories to ensure fresh generation
        processor.builder.run_cmd(
            'rm -rf build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/* build/build_pipelined_d/* build/build_gcd/* || true',
            cwd='/code/workspace',
        )
        print('✅ [V2chisel_batch] Cleaned all build directories for fresh generation')

        # Now generate fresh baseline from pristine code
        baseline_result = processor.baseline_verilog_generator.generate_fresh_baseline()
        if not baseline_result.get('success', False):
            print('❌ [V2chisel_batch] Failed to generate fresh baseline - continuing anyway')
        print('✅ [V2chisel_batch] Fresh baseline generation complete')
        print()

        # Set up processor exactly like real v2chisel_batch
        processor.input_data = input_data
        processor.output_path = args.output

        # CRITICAL: Get the actual container name from Runner and override input_data
        # This ensures the main pipeline uses the same container we set up
        actual_container_name = None
        if hasattr(processor.builder, 'container_manager') and processor.builder.container_manager:
            container_mgr = processor.builder.container_manager
            if hasattr(container_mgr, 'container') and container_mgr.container:
                # Get container name from Docker container object
                actual_container_name = container_mgr.container.name

        if actual_container_name:
            print(f'✅ [V2chisel_batch] Using Runner container: {actual_container_name}')
            input_data['docker_container'] = actual_container_name
        else:
            print('⚠️ [V2chisel_batch] Could not get Runner container name, using default')
            # Instead of using a non-existent container name, let's override all Docker calls
            # The _run_docker_command method will handle routing through Runner
            input_data['docker_container'] = 'runner_managed'  # Placeholder - will be handled by _run_docker_command

        # Run the complete pipeline (this calls all the same methods as real v2chisel_batch)
        result = processor.run(input_data)

        print()
        print('=' * 60)
        print('📊 [V2chisel_batch] PIPELINE RESULTS')
        print('=' * 60)

        # Check the actual success in the v2chisel_batch_with_llm section
        pipeline_results = result.get('v2chisel_batch_with_llm', {}) if result else {}
        total_bugs = pipeline_results.get('total_bugs', 0)

        # Check if pipeline was successful based on the v2chisel_batch_with_llm results
        llm_successes = pipeline_results.get('llm_successes', 0)
        total_bugs = pipeline_results.get('total_bugs', 0)

        if result and total_bugs > 0 and llm_successes > 0:
            print('✅ [V2chisel_batch] PIPELINE SUCCESS: Complete pipeline passed!')

            print('📊 [V2chisel_batch] SUMMARY:')
            print(f'     Total bugs processed: {total_bugs}')
            print(f'     LLM successes: {llm_successes}')
            print(f'     Success rate: {(llm_successes / total_bugs) * 100:.1f}%')

            # Wrap multiline strings for proper YAML output
            result = wrap_literals(result)

            # Save results
            yaml = YAML()
            yaml.default_flow_style = False
            yaml.indent(mapping=2, sequence=4, offset=2)

            with open(args.output, 'w') as out_file:
                yaml.dump(result, out_file)

            print()
            print('🎉 [V2chisel_batch] COMPLETE PIPELINE: SUCCESS!')
            print('The v2chisel_batch pipeline works with real LLM calls.')
            print()
            print(f'📄 [V2chisel_batch] Detailed results saved to: {args.output}')
            return 0
        else:
            print('❌ [V2chisel_batch] PIPELINE FAILURE')
            print(f'Total bugs: {total_bugs}, LLM successes: {llm_successes}')
            return 1

    except Exception as e:
        print(f'💥 [V2chisel_batch] PIPELINE EXCEPTION: {str(e)}')
        if args.debug:
            import traceback

            traceback.print_exc()
        return 1

    finally:
        # CRITICAL: Always restore all files that were modified during the run
        if processor:
            try:
                processor.restore_all_tracked_files()
            except Exception as restore_error:
                print(f'⚠️ [RESTORE] Critical: Failed to restore files: {restore_error}')
                print('💡 [RESTORE] You may need to manually restore Docker files')
        else:
            print('✅ [V2chisel_batch] No processor created - no files to restore')


if __name__ == '__main__':
    exit_code = main()
    print()
    print('=' * 80)
    if exit_code == 0:
        print('🎉 V2CHISEL_BATCH COMPLETED SUCCESSFULLY!')
    else:
        print('💥 V2CHISEL_BATCH FAILED!')
    print('=' * 80)
    sys.exit(exit_code)
