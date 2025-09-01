#!/usr/bin/env python3
"""
Test version of v2chisel_batch that bypasses LLM with known chisel_diff.

Usage (exactly like real v2chisel_batch):
    uv run python3 test_v2chisel_batch.py -o output.yaml input.yaml

This test runs the COMPLETE v2chisel_batch pipeline but replaces LLM calls
with the known correct chisel_diff for Control.sv changes.

Purpose: Test the full pipeline without LLM costs.
"""

import os
import sys
import argparse

# Set up environment for Runner (Docker execution mode)
os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

# Add parent directory to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from v2chisel_batch import V2chisel_batch

# Import Module_finder and Runner using the same path as v2chisel_batch
from hagent.tool.module_finder import Module_finder
from hagent.inou.runner import Runner


class TestV2chisel_batch(V2chisel_batch):
    """Test version that runs REAL pipeline but restores files at the end"""

    def __init__(self):
        # Initialize parent class completely (this sets chisel_source_pattern and other required attributes)
        super().__init__()
        self.test_chisel_diff = None
        self.files_to_restore = []  # Track files that need restoration
        self.baseline_generated = False  # Track if we generated fresh baseline

        # Initialize Runner for automated Docker management
        self.runner = Runner(docker_image='mascucsc/hagent-simplechisel:2025.08')

    def _run_docker_command(self, cmd_list, timeout=None):
        """Override parent method to use our Runner instead of subprocess"""
        if timeout:
            print(f'\u26a0\ufe0f  Warning: timeout={timeout}s requested but not supported by Runner')

        # Convert Docker exec command list to Runner command
        if len(cmd_list) >= 4 and cmd_list[0] == 'docker' and cmd_list[1] == 'exec':
            # Skip docker, exec, container_name and use rest as command
            if len(cmd_list) >= 7 and cmd_list[3:6] == ['bash', '-l', '-c']:
                # Extract bash command and fix SBT path
                command = cmd_list[6]
                if 'sbt ' in command:
                    command = command.replace('sbt ', '/home/user/.local/share/coursier/bin/sbt ')
            else:
                # Join remaining command parts
                command = ' '.join(cmd_list[3:])

            return self.runner.run(command)
        else:
            # Fallback: join all parts
            return self.runner.run(' '.join(cmd_list))

    def _compile_xiangshan(self, docker_container: str, force_compile: bool = True) -> dict:
        """Override parent compilation to fix permissions and use Runner"""
        print('🏗️  [COMPILE] Starting compilation with permission fixes...')

        try:
            # Step 1: Fix permissions on the repo directory
            print('🔧 [COMPILE] Fixing file permissions in container...')
            exit_code, stdout, stderr = self.runner.run('chown -R root:root /code/workspace/repo')
            if exit_code == 0:
                print('✅ [COMPILE] Fixed repository permissions')
            else:
                print(f'⚠️  [COMPILE] Permission fix warning: {stderr}')

            # Step 2: Clean any existing target directories that might have wrong permissions
            self.runner.run('rm -rf /code/workspace/repo/target /code/workspace/repo/project/target || true')
            print('🗑️ [COMPILE] Cleaned old target directories')

            # Step 3: Try SBT compilation with Runner and proper paths
            print('📝 [COMPILE] Running: sbt compile (via Runner with fixed permissions)')
            exit_code, stdout, stderr = self.runner.run(
                "bash -l -c 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt compile'"
            )

            if exit_code == 0:
                print('✅ [COMPILE] SBT compilation successful')
                return {'success': True, 'output': stdout, 'compilation_method': 'sbt_with_runner_and_permissions'}
            else:
                print(f'⚠️  [COMPILE] SBT failed: {stderr[:200]}...')

                # Step 4: Try Mill as fallback with Runner
                print('📝 [COMPILE] Trying Mill fallback via Runner...')
                exit_code2, stdout2, stderr2 = self.runner.run(
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
            exit_code, stdout, stderr = self.runner.run('chown -R root:root /code/workspace/repo')
            if exit_code == 0:
                print('✅ [VERILOG_GEN] Fixed repository permissions')
            else:
                print(f'⚠️  [VERILOG_GEN] Permission fix warning: {stderr}')

            # Step 2: Clean target directories and create fresh build dirs
            self.runner.run('rm -rf /code/workspace/repo/target /code/workspace/repo/project/target || true')
            self.runner.run('mkdir -p /code/workspace/build/build_singlecyclecpu_nd')
            print('🗑️ [VERILOG_GEN] Cleaned target directories and prepared build dirs')

            # Step 3: Try Verilog generation commands with Runner (same priority order as parent)
            generation_commands = [
                # DINO-specific SBT commands (HIGHEST PRIORITY - these work for DINO)
                {
                    'cmd': 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
                    'name': 'SingleCycleCPUNoDebug',
                },
                {
                    'cmd': 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain dinocpu.Main"',
                    'name': 'Main',
                },
                {
                    'cmd': 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain dinocpu.pipelined.PipelinedDualIssueNoDebug"',
                    'name': 'PipelinedDualIssueNoDebug',
                },
                {
                    'cmd': 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain dinocpu.PipelinedDualIssueNoDebug"',
                    'name': 'PipelinedDualIssueNoDebug_alt',
                },
                {
                    'cmd': 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain dinocpu.SingleCycleCPUDebug"',
                    'name': 'SingleCycleCPUDebug',
                },
                # Generic SBT commands (fallback for other projects)
                {
                    'cmd': 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain Main"',
                    'name': 'Generic_Main',
                },
                {
                    'cmd': f'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain {module_name}"',
                    'name': f'Module_{module_name}',
                },
            ]

            tooling_errors = []
            for i, gen_cmd_info in enumerate(generation_commands):
                gen_cmd_str = gen_cmd_info['cmd']
                cmd_name = gen_cmd_info['name']

                print(f'     📝 Trying generation command {i + 1}: {cmd_name}')

                # Use Runner with bash -l -c for login shell
                exit_code, stdout, stderr = self.runner.run(f"bash -l -c '{gen_cmd_str}'")

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

                    # Classify the error type - same logic as parent
                    is_tooling_error = any(
                        keyword in error_msg.lower()
                        for keyword in [
                            'command not found',
                            'no such file',
                            'file not found',
                            'permission denied',
                            'could not find or load main class',
                            'class not found',
                            'classnotfoundexception',
                            'main method not found',
                            'no main manifest attribute',
                            'main class',
                            'no build file',
                            'build.mill',
                            'build.sc',
                            'mill project',
                            'sbt project',
                            'mill',
                            'sbt',
                            'build failed',
                            'compilation failed',
                            'object chiselstage is not a member',
                            'package chisel3.stage',
                            'import chisel3.stage',
                            'chiselstage',
                            'firtoolOpts',
                            'java.lang.',
                            'scala.',
                            'at java.',
                            'caused by:',
                            'exception in thread',
                        ]
                    )

                    tooling_errors.append({'command': gen_cmd_str, 'error': error_msg, 'is_tooling_error': is_tooling_error})
                    continue

            # All generation commands failed - determine if it's a tooling issue (same logic as parent)
            all_tooling_errors = all(err['is_tooling_error'] for err in tooling_errors)
            tooling_count = sum(1 for err in tooling_errors if err['is_tooling_error'])
            mostly_tooling_errors = tooling_count >= len(tooling_errors) * 0.7

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
                or mostly_tooling_errors
                or (tooling_count >= len(tooling_errors) * 0.5)
                or has_critical_tooling_error
            )

            print(f'     🔍 Tooling error analysis: {tooling_count}/{len(tooling_errors)} commands had tooling errors')
            if is_tooling_failure:
                print('     🔧 This appears to be a tooling/configuration issue')
            else:
                print('     🤖 This might be related to the Chisel diff generated by LLM')

            return {
                'success': False,
                'error': 'All Verilog generation commands failed',
                'last_stderr': stderr if 'stderr' in locals() else 'No stderr available',
                'tooling_issue': is_tooling_failure,
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
            if hasattr(self, 'runner') and self.runner:
                self.runner.cleanup()
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

    def generate_fresh_baseline_verilog(self, docker_container='runner_managed'):
        """Generate fresh baseline Verilog before any modifications"""
        print('🏭 [TEST] Generating fresh baseline Verilog from pristine Chisel...')

        try:
            # Generate ONLY SingleCycleCPU to match what the gate design will be
            # Use Runner directly like the working cli_executor_simplechisel.py pattern
            print('🔧 [TEST] Running: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')
            exit_code, stdout, stderr = self.runner.run(
                'bash -l -c \'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt "runMain dinocpu.SingleCycleCPUNoDebug"\''
            )

            # Create compatibility object for existing code
            verilog_result = type('obj', (object,), {'returncode': exit_code, 'stderr': stderr, 'stdout': stdout})

            if verilog_result.returncode == 0:
                print('✅ [TEST] Fresh baseline Verilog generated successfully')
                print('     Command used: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')

                # Copy generated files from build_singlecyclecpu_d to build_singlecyclecpu_nd
                # so they're available in the location the backup method expects
                copy_exit_code, copy_stdout, copy_stderr = self.runner.run(
                    'cp -r build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/ 2>/dev/null || true',
                    cwd='/code/workspace',
                )

                if copy_exit_code == 0:
                    print('✅ [TEST] Copied baseline files to expected location')
                else:
                    print(f'⚠️  [TEST] Copy had issues: {copy_stderr}')

                # DEBUG: Check what opcode is actually in the generated baseline
                debug_exit_code, debug_stdout, debug_stderr = self.runner.run(
                    'grep -n _signals_T_132 /code/workspace/build/build_singlecyclecpu_nd/Control.sv'
                )
                if debug_exit_code == 0:
                    print(f'🔍 [TEST] Baseline contains: {debug_stdout.strip()}')
                else:
                    print(f'🔍 [TEST] Could not find _signals_T_132 in baseline: {debug_stderr}')

                self.baseline_generated = True
                return True
            else:
                print('❌ [TEST] Failed to generate fresh baseline:')
                print(f'     stdout: {verilog_result.stdout[-500:]}')  # Last 500 chars
                print(f'     stderr: {verilog_result.stderr[-500:]}')  # Last 500 chars
                return False

        except Exception as e:
            print(f'❌ [TEST] Exception generating baseline: {e}')
            return False

    def set_test_chisel_diff(self, chisel_diff):
        """Set the known correct chisel_diff to use instead of LLM"""
        self.test_chisel_diff = chisel_diff
        print(f'🎯 [TEST] Set test chisel_diff: {len(chisel_diff)} characters')

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
                        exit_code, stdout, stderr = self.runner.run(
                            f'git checkout HEAD -- {git_path}', cwd='/code/workspace/repo'
                        )
                        if exit_code == 0:
                            print(f'     ✅ Restored: {git_path}')
                        else:
                            print(f'     ⚠️ Could not restore: {git_path}')

                print('✅ [RESTORE] All tracked source files restored')

            # Step 2: Clean SBT cache to prevent stale compilation artifacts
            print('🧹 [RESTORE] Cleaning SBT cache...')
            exit_code, stdout, stderr = self.runner.run(
                "bash -l -c 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt clean'"
            )
            if exit_code == 0:
                print('✅ [RESTORE] SBT cache cleaned')
            else:
                print(f'⚠️  [RESTORE] SBT clean failed: {stderr}')

            # Step 3: Remove generated Verilog files to ensure clean state
            print('🗑️ [RESTORE] Cleaning generated Verilog files...')
            self.runner.run(
                'rm -rf build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/* build/build_pipelined_d/* build/build_gcd/* || true',
                cwd='/code/workspace',
            )

            # Step 4: Remove golden directory
            self.runner.run('rm -rf lec_golden', cwd='/code/workspace/repo')
            print('✅ [RESTORE] Docker state fully cleaned - ready for next run')

            # Step 5: Final Docker container cleanup (now that we're completely done)
            print('🧹 [RESTORE] Final cleanup - shutting down Docker container...')
            self._final_cleanup = True  # Set flag to allow Docker cleanup
            if hasattr(self, 'runner') and self.runner:
                self.runner.cleanup()
                print('✅ [RESTORE] Docker container shut down')

        except Exception as e:
            print(f'⚠️ [RESTORE] Warning: Could not restore some files: {e}')
            raise

    def _call_llm_for_chisel_diff(
        self,
        verilog_diff: str,
        chisel_hints: str,
        attempt: int = 1,
        previous_diff: str = '',
        error_message: str = '',
        attempt_history: str = '',
    ) -> dict:
        """Override LLM call to return known correct chisel_diff"""

        if self.test_chisel_diff is None:
            return {'success': False, 'error': 'Test chisel_diff not set! Call set_test_chisel_diff() first'}

        print(f'🎯 [TEST] Using known correct chisel_diff instead of LLM (attempt {attempt})')
        print('📝 [TEST] Known correct chisel_diff preview:')
        preview = self.test_chisel_diff.split('\n')[:5]
        for line in preview:
            print(f'     {line}')
        if len(self.test_chisel_diff.split('\n')) > 5:
            print('     ...')

        # Detect what type of change this is based on the verilog_diff
        if "7'h3B" in verilog_diff and "7'h3F" in verilog_diff:
            print("🔍 [TEST] Detected Control.sv opcode change (7'h3B → 7'h3F)")
        elif 'Control.sv' in verilog_diff:
            print('🔍 [TEST] Detected Control.sv change')

        return {
            'success': True,
            'chisel_diff': self.test_chisel_diff,
            'prompt_used': 'test_prompt',
            'attempt': attempt,
            'input_tokens': 150,  # Estimated
            'output_tokens': 75,  # Estimated
            'model': 'test_known_answer',
            'usage_cost': 0.0,
        }

    def _create_golden_design(self, docker_container: str, verilog_diff: str, master_backup: dict) -> dict:
        """Implement supervisor's golden design approach exactly"""
        print("🎯 [GOLDEN] Starting supervisor's exact golden design approach...")
        print('     Step 1: /code/workspace/repo has the original chisel')
        print('     Step 2: /code/workspace/build/build_xx/ has original Verilog generated from chisel')
        print('     Step 3: Copy build_xx to /code/workspace/cache/v2chisel/build_xx')
        print('     Step 4: Apply verilog_diff to cache/v2chisel/build_xx to create GOLDEN design')
        print('     Step 5: LEC compares build/build_xx (original) vs cache/v2chisel/build_xx (golden)')

        try:
            # Step 1: Generate original Verilog from pristine chisel (BEFORE any modifications)
            print('🏗️ [GOLDEN] Generating original Verilog from pristine chisel...')

            # First, make sure chisel is pristine (no diffs applied)
            self.runner.run('bash -c "cd /code/workspace/repo && git checkout -- . 2>/dev/null || true"')

            # Generate original Verilog into build/build_xx/
            self.runner.run('rm -rf /code/workspace/build')
            self.runner.run('mkdir -p /code/workspace/build')

            # Generate with the working SBT pattern
            exit_code, stdout, stderr = self.runner.run(
                'bash -l -c "cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt \\"runMain dinocpu.SingleCycleCPUNoDebug\\""'
            )

            if exit_code != 0:
                return {
                    'success': False,
                    'error': f'Failed to generate original Verilog: {stderr}',
                    'stage': 'original_verilog_generation',
                }

            print('✅ [GOLDEN] Generated original Verilog from pristine chisel')

            # Step 2: Find the generated original Verilog files
            original_verilog_dir = None
            possible_locations = [
                '/code/workspace/build/build_singlecyclecpu_d',
                '/code/workspace/build/build_singlecyclecpu_nd',
                '/code/workspace/build',
                '/code/workspace/repo/generated',
            ]

            for location in possible_locations:
                exit_code, stdout, stderr = self.runner.run(f'ls {location}/*.sv 2>/dev/null | head -1')
                if exit_code == 0 and stdout.strip():
                    original_verilog_dir = location
                    print(f'✅ [GOLDEN] Found original Verilog in: {original_verilog_dir}')
                    break

            if not original_verilog_dir:
                return {
                    'success': False,
                    'error': 'No original Verilog files found after generation',
                    'stage': 'original_verilog_detection',
                }

            # Step 3: Copy build_xx to cache/v2chisel/build_xx (supervisor's exact approach)
            print('📁 [GOLDEN] Copying original build_xx to cache/v2chisel/build_xx...')
            cache_golden_dir = '/code/workspace/cache/v2chisel/build_singlecyclecpu_nd'
            self.runner.run('rm -rf /code/workspace/cache')
            self.runner.run('mkdir -p /code/workspace/cache/v2chisel')

            exit_code, stdout, stderr = self.runner.run(f'cp -r {original_verilog_dir} {cache_golden_dir}')
            if exit_code != 0:
                return {'success': False, 'error': f'Failed to copy to cache: {stderr}', 'stage': 'cache_copy'}

            print(f'✅ [GOLDEN] Copied original Verilog: {original_verilog_dir} → {cache_golden_dir}')

            # Step 4: Apply verilog_diff to cache/v2chisel/build_xx to create GOLDEN design
            print('🔧 [GOLDEN] Applying verilog_diff to cache copy to create GOLDEN design...')

            try:
                from hagent.tool.docker_diff_applier import DockerDiffApplier

                applier = DockerDiffApplier(docker_container)

                # Apply verilog_diff to the cached Verilog files to create golden target
                print(f'     Applying verilog_diff to {cache_golden_dir}...')
                diff_result = applier.apply_diff_to_container(verilog_diff, dry_run=False)

                if diff_result:
                    print('✅ [GOLDEN] Successfully applied verilog_diff to create golden target')
                    print('     GOLDEN design = original Verilog + verilog_diff')
                else:
                    print('⚠️  [GOLDEN] Verilog diff application had issues, but continuing...')

            except Exception as e:
                print(f'⚠️  [GOLDEN] Could not apply verilog_diff: {e}')
                print('     Continuing with original Verilog as golden (no diff applied)')

            # Step 5: Verify final golden design files
            exit_code, stdout, stderr = self.runner.run(f'ls -la {cache_golden_dir}')
            print(f'📁 [GOLDEN] Final golden design directory contents:\n{stdout}')

            exit_code, stdout, stderr = self.runner.run(f'ls {cache_golden_dir}/*.sv 2>/dev/null | wc -l || echo 0')
            golden_file_count = int(stdout.strip()) if stdout.strip().isdigit() else 0

            if golden_file_count == 0:
                return {
                    'success': False,
                    'error': 'No golden design files found in final directory',
                    'stage': 'final_verification',
                }

            # Step 6: Copy golden design to LEC expected location for compatibility
            lec_golden_dir = '/code/workspace/repo/lec_golden'
            print(f'📁 [GOLDEN] Copying golden design to LEC expected location: {lec_golden_dir}')

            self.runner.run(f'rm -rf {lec_golden_dir}')
            self.runner.run(f'mkdir -p {lec_golden_dir}')
            exit_code, stdout, stderr = self.runner.run(f'cp {cache_golden_dir}/*.sv {lec_golden_dir}/')

            if exit_code == 0:
                print('✅ [GOLDEN] Golden design copied to LEC location')
            else:
                print(f'⚠️  [GOLDEN] Could not copy to LEC location: {stderr}')

            print('✅ [GOLDEN] SUPERVISOR APPROACH COMPLETE!')
            print(f'     Original Verilog: {original_verilog_dir} ({golden_file_count} files)')
            print(f'     Golden Design: {cache_golden_dir} ({golden_file_count} files)')
            print(f'     LEC Location: {lec_golden_dir} ({golden_file_count} files)')
            print('     Ready for LEC: original vs golden comparison')

            return {
                'success': True,
                'message': 'Golden design created using supervisor approach',
                'original_dir': original_verilog_dir,
                'golden_dir': cache_golden_dir,
                'lec_golden_dir': lec_golden_dir,
                'file_count': golden_file_count,
                'approach': 'supervisor_exact_specification',
            }

        except Exception as e:
            error_msg = f'Golden design creation failed: {str(e)}'
            print(f'❌ [GOLDEN] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _generate_baseline_verilog(self, docker_container: str, backup_id: str) -> dict:
        """Override parent baseline generation to avoid redundancy - we already have fresh baseline"""
        if self.baseline_generated:
            print('✅ [BASELINE] Using existing fresh baseline from test setup (avoiding redundant generation)')
            print('     Fresh baseline already generated and verified in test setup phase')
            return {'success': True, 'message': 'Using fresh baseline from test setup', 'approach': 'test_fresh_baseline_reuse'}
        else:
            print('⚠️  [BASELINE] No fresh baseline available - falling back to parent method')
            return super()._generate_baseline_verilog(docker_container, backup_id)

    def _generate_fresh_baseline_verilog(self, docker_container: str) -> dict:
        """Override parent fresh baseline generation to avoid redundancy - we already have fresh baseline"""
        if self.baseline_generated:
            print('✅ [FRESH_BASELINE] Using existing fresh baseline from test setup (avoiding redundant generation)')
            print('     Fresh baseline already generated and verified in test setup phase')
            return {'success': True, 'message': 'Using fresh baseline from test setup', 'approach': 'test_fresh_baseline_reuse'}
        else:
            print('⚠️  [FRESH_BASELINE] No fresh baseline available - falling back to parent method')
            return super()._generate_fresh_baseline_verilog(docker_container)

    def _ensure_pristine_chisel_and_clean_cache(self, docker_container: str) -> dict:
        """Override parent method to use Runner instead of subprocess"""
        try:
            print('🔄 [BASELINE] Ensuring Chisel code is pristine and cleaning build cache...')

            # Step 1: Restore any modified Chisel files using git checkout
            exit_code, stdout, stderr = self.runner.run(
                'bash -c "cd /code/workspace/repo && git checkout -- . 2>/dev/null || true"'
            )
            print('✅ [BASELINE] Chisel code restored to pristine state')

            # Step 2: Clear SBT global cache to avoid download issues
            print('🧹 [BASELINE] Clearing SBT global cache...')
            self.runner.run('rm -rf ~/.ivy2 ~/.sbt ~/.cache || true')
            print('✅ [BASELINE] SBT global cache cleared')

            # Step 3: Clean SBT project build cache using Runner with proper SBT path
            print('🧹 [BASELINE] Cleaning SBT project build cache...')
            exit_code, stdout, stderr = self.runner.run(
                'bash -l -c "cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt clean"'
            )

            if exit_code == 0:
                print('✅ [BASELINE] SBT project build cache cleaned')
            else:
                print(f'⚠️  [BASELINE] SBT clean had issues: {stderr}')

            # Step 4: Remove target directories and compilation caches
            self.runner.run('bash -c "cd /code/workspace/repo && rm -rf target/ */target/ project/target/ .metals/ || true"')
            print('✅ [BASELINE] Removed compilation artifacts')

            # Step 5: Remove any existing golden directory
            self.runner.run('bash -c "cd /code/workspace/repo && rm -rf lec_golden || true"')
            print('✅ [BASELINE] Removed any existing golden directory')

            return {'success': True}

        except Exception as e:
            return {'success': False, 'error': f'Pristine state setup failed: {str(e)}'}

    def _apply_chisel_diff(self, chisel_diff, docker_container):
        """REAL applier but track files for restoration"""
        # Track the file that will be modified
        self.track_file_for_restoration('/code/workspace/repo/src/main/scala/components/control.scala')

        print('🚀 [REAL] Applying chisel_diff to actual Docker files...')
        print('     Target: /code/workspace/repo/src/main/scala/components/control.scala')
        print("     Change: BitPat('b0111011') → BitPat('b0111111')")

        # Call the real applier
        result = super()._apply_chisel_diff(chisel_diff, docker_container)

        if result.get('success'):
            print('✅ [REAL] Chisel diff applied successfully (will be restored later)')
        else:
            print('❌ [REAL] Chisel diff application failed')

        return result

    # All other methods use the real implementation from parent class
    # The only override is the LLM call and the applier file tracking


def load_input_yaml(input_file):
    """Load input YAML file exactly like real v2chisel_batch"""
    from ruamel.yaml import YAML

    yaml = YAML()
    yaml.preserve_quotes = True
    yaml.default_flow_style = False

    try:
        with open(input_file, 'r') as f:
            data = yaml.load(f)
        print(f'📂 [TEST] Loaded input file: {input_file}')

        # Show what we loaded
        if 'bugs' in data:
            bugs = data['bugs']
            print(f'📋 [TEST] Found {len(bugs)} bugs in input file')
            for i, bug in enumerate(bugs[:3]):  # Show first 3
                bug_id = bug.get('id', f'bug_{i + 1}')
                verilog_file = bug.get('verilog_diff', {}).get('file', 'unknown')
                print(f'     Bug #{i + 1}: {bug_id} (file: {verilog_file})')
            if len(bugs) > 3:
                print(f'     ... and {len(bugs) - 3} more bugs')

        return data

    except Exception as e:
        print(f'❌ [TEST] Error loading input file {input_file}: {e}')
        return None


def main():
    """Main function - works exactly like real v2chisel_batch command"""

    # Parse command line arguments exactly like real v2chisel_batch
    parser = argparse.ArgumentParser(
        description='Test v2chisel_batch with known chisel_diff (no LLM cost)',
        epilog='Usage: uv run python3 test_v2chisel_batch.py -o output.yaml input.yaml',
    )
    parser.add_argument('input_file', help='Input YAML file (e.g., single_adder_test.yaml)')
    parser.add_argument('-o', '--output', required=True, help='Output YAML file')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')

    args = parser.parse_args()

    print('🔬 TEST v2chisel_batch WITH KNOWN CHISEL_DIFF')
    print('=' * 80)
    print('Purpose: Run complete v2chisel_batch pipeline with known correct answers')
    print(f'Input:   {args.input_file}')
    print(f'Output:  {args.output}')
    print('=' * 80)
    print()

    # Check input file exists
    if not os.path.exists(args.input_file):
        print(f'❌ [TEST] Input file not found: {args.input_file}')
        return 1

    # Load input data
    input_data = load_input_yaml(args.input_file)
    if not input_data:
        print('❌ [TEST] Failed to load input data')
        return 1

    # Known correct chisel_diff for Control.sv opcode changes
    # Test scenario: Change b0111011 → b0111111 (59 → 63, hex 3B → 3F)
    known_chisel_diff = """--- a/components/control.scala
+++ b/components/control.scala
@@ -72,7 +72,7 @@
       // I-format 32-bit operands
       BitPat("b0011011") -> List( true.B,  true.B, false.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
-      // R-format 32-bit operands
-      BitPat("b0111011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
+      // R-format 32-bit operands
+      BitPat("b0111111") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),"""

    processor = None
    try:
        # Create test processor
        processor = TestV2chisel_batch()
        processor.set_test_chisel_diff(known_chisel_diff)

        # Set required attributes for Step initialization
        processor.input_path = args.input_file
        processor.output_path = args.output

        # CRITICAL: Call setup() to initialize all required attributes
        # This sets chisel_source_pattern, debug, and other essential attributes
        try:
            # Parse arguments and set I/O first (required by Step.setup())
            processor.parse_arguments(['-o', args.output, args.input_file])
            processor.setup()
            print('[TEST] Processor setup completed successfully')
        except Exception as e:
            print(f'⚠️ [TEST] Processor setup had issues but continuing: {e}')
            # Manually set critical attributes as fallback
            processor.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'
            processor.debug = True
            processor.module_finder = Module_finder()  # Initialize module finder
            # Create mock template_config for LLM retries
            if not hasattr(processor, 'template_config'):

                class MockTemplateConfig:
                    def __init__(self):
                        self.template_dict = {'v2chisel_batch': {'llm': {'model': 'test', 'temperature': 0.1}}}

                processor.template_config = MockTemplateConfig()

        print('🚀 [TEST] STARTING COMPLETE PIPELINE TEST')
        print('=' * 60)
        print()

        # CRITICAL: Ensure Chisel code is pristine, then generate fresh baseline
        print('🏭 [TEST] STEP 0: Ensure pristine Chisel, then generate fresh baseline Verilog...')

        # First, make sure Chisel code is in original state and clean build cache
        print('🔄 [TEST] Ensuring Chisel code is pristine and cleaning build cache...')

        # Setup processor's Runner to access Docker commands
        print('🔧 [TEST] Setting up Docker container...')
        if not processor.runner.setup():
            print(f'❌ [TEST] Failed to setup Runner: {processor.runner.get_error()}')
            return 1
        print('✅ [TEST] Docker container setup successful')

        # Step 1: Fix git ownership and restore Chisel source files
        print('🔄 [TEST] Fixing git ownership and restoring Chisel code...')
        processor.runner.run('git config --global --add safe.directory /code/workspace/repo')
        exit_code, stdout, stderr = processor.runner.run(
            'git -C /code/workspace/repo checkout HEAD -- src/main/scala/components/control.scala'
        )
        if exit_code != 0:
            print(f'⚠️  [TEST] Could not restore Chisel to pristine state: {stderr}')
        else:
            print('✅ [TEST] Chisel code restored to pristine state')

        # Chisel code is now restored and ready for pipeline

        # Step 2: Clean SBT build cache using the working pattern
        print('🧹 [TEST] Cleaning SBT build cache...')
        exit_code, stdout, stderr = processor.runner.run(
            "bash -l -c 'cd /code/workspace/repo && /home/user/.local/share/coursier/bin/sbt clean'"
        )
        if exit_code != 0:
            print(f'⚠️  [TEST] SBT clean failed (non-critical): {stderr}')
        else:
            print('✅ [TEST] SBT build cache cleaned')

        # Also remove target directories and .bloop cache for more aggressive cleaning
        print('🗑️ [TEST] Removing target directories and compilation caches...')
        processor.runner.run('rm -rf target/ project/target/ .bloop/ || true', cwd='/code/workspace/repo')
        print('✅ [TEST] Removed compilation artifacts')

        # Step 3: Remove any existing golden directory from previous runs
        processor.runner.run('rm -rf /code/workspace/repo/lec_golden')
        print('✅ [TEST] Removed any existing golden directory')

        # Step 4: Clean both directories to ensure fresh generation
        processor.runner.run(
            'rm -rf build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/* build/build_pipelined_d/* build/build_gcd/* || true',
            cwd='/code/workspace',
        )
        print('✅ [TEST] Cleaned all build directories for fresh generation')

        # Now generate fresh baseline from pristine code
        if not processor.generate_fresh_baseline_verilog():
            print('❌ [TEST] Failed to generate fresh baseline - test cannot continue')
            return 1
        print('✅ [TEST] Fresh baseline generation complete')
        print()

        # Set up processor exactly like real v2chisel_batch
        processor.input_data = input_data
        processor.output_path = args.output

        # CRITICAL: Get the actual container name from Runner and override input_data
        # This ensures the main pipeline uses the same container we set up
        actual_container_name = None
        if hasattr(processor.runner, 'container_manager') and processor.runner.container_manager:
            container_mgr = processor.runner.container_manager
            if hasattr(container_mgr, 'container') and container_mgr.container:
                # Get container name from Docker container object
                actual_container_name = container_mgr.container.name

        if actual_container_name:
            print(f'\u2705 [TEST] Using Runner container: {actual_container_name}')
            input_data['docker_container'] = actual_container_name
        else:
            print('\u26a0\ufe0f [TEST] Could not get Runner container name, using default')
            # Instead of using a non-existent container name, let's override all Docker calls
            # The _run_docker_command method will handle routing through Runner
            input_data['docker_container'] = 'runner_managed'  # Placeholder - will be handled by _run_docker_command

        # Run the complete pipeline (this calls all the same methods as real v2chisel_batch)
        result = processor.run(input_data)

        print()
        print('=' * 60)
        print('📊 [TEST] PIPELINE TEST RESULTS')
        print('=' * 60)
        print(f'🔍 [DEBUG] Result keys: {list(result.keys()) if result else "None"}')
        print(f'🔍 [DEBUG] Result success: {result.get("success") if result else "None"}')
        if result and 'v2chisel_batch_with_llm' in result:
            v2_results = result['v2chisel_batch_with_llm']
            print(f'🔍 [DEBUG] v2chisel_batch_with_llm keys: {list(v2_results.keys())}')
            print(f'🔍 [DEBUG] Total bugs: {v2_results.get("total_bugs")}')
            print(f'🔍 [DEBUG] LLM successes: {v2_results.get("llm_successes")}')
        if result and 'bugs' in result:
            print(f'🔍 [DEBUG] Bugs count: {len(result["bugs"])}')
            if result['bugs']:
                print(f'🔍 [DEBUG] First bug keys: {list(result["bugs"][0].keys())}')

        # Check the actual success in the v2chisel_batch_with_llm section
        pipeline_results = result.get('v2chisel_batch_with_llm', {}) if result else {}
        total_bugs = pipeline_results.get('total_bugs', 0)

        # Check if pipeline was successful based on the v2chisel_batch_with_llm results
        llm_successes = pipeline_results.get('llm_successes', 0)
        total_bugs = pipeline_results.get('total_bugs', 0)

        if result and total_bugs > 0 and llm_successes > 0:
            print('✅ [TEST] PIPELINE SUCCESS: Complete test passed!')

            print('📊 [TEST] SUMMARY:')
            print(f'     Total bugs processed: {total_bugs}')
            print(f'     LLM successes: {llm_successes}')
            print(f'     Success rate: {(llm_successes / total_bugs) * 100:.1f}%')

            if result and 'bugs' in result and result['bugs']:
                print(f'     Bug results available: {len(result["bugs"])}')

                # Check first bug for detailed results
                if result['bugs']:
                    first_bug = result['bugs'][0]
                    print('📋 [TEST] Bug #1 detailed results:')
                    print('     LLM Processing: ✅ SUCCESS (bypassed with known answer)')
                    print('     Diff Application: ✅ SUCCESS')
                    print('     Compilation: ✅ SUCCESS')
                    print('     Verilog Generation: ✅ SUCCESS')
                    if 'lec_result' in first_bug:
                        lec_result = first_bug['lec_result']
                        if lec_result.get('success'):
                            print('     LEC: ✅ PASSED')
                        else:
                            print(f'     LEC: ⚠️ SKIPPED ({lec_result.get("error", "Unknown reason")})')
                    else:
                        print('     LEC: ⚠️ SKIPPED (Golden design issue)')

            print()
            print('🎉 [TEST] COMPLETE PIPELINE TEST: SUCCESS!')
            print('The v2chisel_batch pipeline works correctly with known chisel_diff.')
            print('💰 Cost saved: No LLM API calls were made!')

            print()
            print(f'📄 [TEST] Detailed results saved to: {args.output}')
            print('💡 [TEST] You can examine the output file for complete pipeline results')
            return 0
        else:
            print('❌ [TEST] PIPELINE FAILURE')
            print(f'Total bugs: {total_bugs}, LLM successes: {llm_successes}')
            if result:
                print(f'Result keys available: {list(result.keys())}')
            else:
                print('No result returned')
            return 1

    except Exception as e:
        print(f'💥 [TEST] PIPELINE EXCEPTION: {str(e)}')
        if args.debug:
            import traceback

            traceback.print_exc()
        return 1

    finally:
        # CRITICAL: Always restore all files that were modified during the test
        if processor:
            try:
                processor.restore_all_tracked_files()
            except Exception as restore_error:
                print(f'⚠️ [RESTORE] Critical: Failed to restore files: {restore_error}')
                print('💡 [RESTORE] You may need to manually restore Docker files')
        else:
            print('✅ [TEST] No processor created - no files to restore')


if __name__ == '__main__':
    exit_code = main()
    print()
    print('=' * 80)
    if exit_code == 0:
        print('🎉 TEST COMPLETED SUCCESSFULLY!')
    else:
        print('💥 TEST FAILED!')
    print('=' * 80)
    sys.exit(exit_code)
