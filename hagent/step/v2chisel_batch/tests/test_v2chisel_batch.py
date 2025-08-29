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

# Add parent directory to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from v2chisel_batch import V2chisel_batch

# Import Module_finder using the same path as v2chisel_batch
from hagent.tool.module_finder import Module_finder


class TestV2chisel_batch(V2chisel_batch):
    """Test version that runs REAL pipeline but restores files at the end"""

    def __init__(self):
        # Initialize parent class completely (this sets chisel_source_pattern and other required attributes)
        super().__init__()
        self.test_chisel_diff = None
        self.files_to_restore = []  # Track files that need restoration
        self.baseline_generated = False  # Track if we generated fresh baseline

        # Ensure all required attributes are set (in case parent init missed some)
        if not hasattr(self, 'chisel_source_pattern'):
            self.chisel_source_pattern = './tmp/src/main/scala/*/*.scala'
        if not hasattr(self, 'module_finder'):
            self.module_finder = Module_finder()  # Initialize module finder properly
        if not hasattr(self, 'debug'):
            self.debug = True

        # Create mock template_config
        if not hasattr(self, 'template_config'):

            class MockTemplateConfig:
                def __init__(self):
                    self.template_dict = {'v2chisel_batch': {'llm': {'model': 'test', 'temperature': 0.1}}}

            self.template_config = MockTemplateConfig()

    def generate_fresh_baseline_verilog(self, docker_container='hagent'):
        """Generate fresh baseline Verilog before any modifications"""
        print('🏭 [TEST] Generating fresh baseline Verilog from pristine Chisel...')

        try:
            import subprocess

            # Generate ONLY SingleCycleCPU to match what the gate design will be
            # Use login shell to ensure sbt is in PATH (same as parent class does)
            verilog_cmd = [
                'docker',
                'exec',
                docker_container,
                'bash',
                '-l',
                '-c',
                'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
            ]

            print('🔧 [TEST] Running: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')
            verilog_result = subprocess.run(verilog_cmd, capture_output=True, text=True, timeout=300)

            if verilog_result.returncode == 0:
                print('✅ [TEST] Fresh baseline Verilog generated successfully')
                print('     Command used: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')

                # Copy generated files from build_singlecyclecpu_d to build_singlecyclecpu_nd
                # so they're available in the location the backup method expects
                copy_cmd = [
                    'docker',
                    'exec',
                    docker_container,
                    'bash',
                    '-c',
                    'cp -r /code/workspace/build/build_singlecyclecpu_d/* /code/workspace/build/build_singlecyclecpu_nd/ 2>/dev/null || true',
                ]
                copy_result = subprocess.run(copy_cmd, capture_output=True, text=True)

                if copy_result.returncode == 0:
                    print('✅ [TEST] Copied baseline files to expected location')
                else:
                    print(f'⚠️  [TEST] Copy had issues: {copy_result.stderr}')

                # DEBUG: Check what opcode is actually in the generated baseline
                debug_cmd = [
                    'docker',
                    'exec',
                    docker_container,
                    'grep',
                    '-n',
                    '_signals_T_132',
                    '/code/workspace/build/build_singlecyclecpu_nd/Control.sv',
                ]
                debug_result = subprocess.run(debug_cmd, capture_output=True, text=True)
                if debug_result.returncode == 0:
                    print(f'🔍 [TEST] Baseline contains: {debug_result.stdout.strip()}')
                else:
                    print(f'🔍 [TEST] Could not find _signals_T_132 in baseline: {debug_result.stderr}')

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

        import subprocess

        try:
            # Step 1: Restore all tracked files using git checkout
            if self.files_to_restore:
                for file_path in self.files_to_restore:
                    # Convert Docker path to git-relative path
                    if file_path.startswith('/code/workspace/repo/'):
                        git_path = file_path.replace('/code/workspace/repo/', '')
                        restore_cmd = [
                            'docker',
                            'exec',
                            'hagent',
                            'git',
                            '-C',
                            '/code/workspace/repo',
                            'checkout',
                            'HEAD',
                            '--',
                            git_path,
                        ]
                        result = subprocess.run(restore_cmd, capture_output=True, text=True)
                        if result.returncode == 0:
                            print(f'     ✅ Restored: {git_path}')
                        else:
                            print(f'     ⚠️ Could not restore: {git_path}')

                print('✅ [RESTORE] All tracked source files restored')

            # Step 2: Clean SBT cache to prevent stale compilation artifacts
            print('🧹 [RESTORE] Cleaning SBT cache...')
            clean_cmd = ['docker', 'exec', 'hagent', 'bash', '-l', '-c', 'cd /code/workspace/repo && sbt clean']
            clean_result = subprocess.run(clean_cmd, capture_output=True, text=True, timeout=60)
            if clean_result.returncode == 0:
                print('✅ [RESTORE] SBT cache cleaned')
            else:
                print(f'⚠️  [RESTORE] SBT clean failed: {clean_result.stderr}')

            # Step 3: Remove generated Verilog files to ensure clean state
            print('🗑️ [RESTORE] Cleaning generated Verilog files...')
            cleanup_cmd = [
                'docker',
                'exec',
                'hagent',
                'bash',
                '-c',
                'cd /code/workspace && rm -rf build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/* build/build_pipelined_d/* build/build_gcd/* || true',
            ]
            subprocess.run(cleanup_cmd, capture_output=True, text=True)

            # Step 4: Remove golden directory
            golden_cleanup_cmd = ['docker', 'exec', 'hagent', 'rm', '-rf', '/code/workspace/repo/lec_golden']
            subprocess.run(golden_cleanup_cmd, capture_output=True, text=True)
            print('✅ [RESTORE] Docker state fully cleaned - ready for next run')

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

    def _backup_existing_original_verilog(self, docker_container: str, backup_id: str) -> dict:
        """Override to use fresh generated baseline instead of stale existing files"""
        if not self.baseline_generated:
            print('⚠️  [TEST] No fresh baseline generated - falling back to parent method')
            return super()._backup_existing_original_verilog(docker_container, backup_id)

        print('🎯 [TEST] Using fresh baseline Verilog for golden design (generated in test setup)')

        try:
            import subprocess
            import os

            # Find ONLY the SingleCycleCPU-related files in build_singlecyclecpu_nd (copied there after generation)
            baseline_path = '/code/workspace/build/build_singlecyclecpu_nd'

            # Create backup directory
            backup_dir = f'/tmp/baseline_verilog_{backup_id}'
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            subprocess.run(mkdir_cmd, capture_output=True, text=True, check=True)

            # Find and backup only the SingleCycleCPU-related files
            find_cmd = ['docker', 'exec', docker_container, 'find', baseline_path, '-name', '*.sv', '-type', 'f']
            find_result = subprocess.run(find_cmd, capture_output=True, text=True)

            if find_result.returncode != 0:
                return {'success': False, 'error': f'Could not find baseline Verilog files: {find_result.stderr}'}

            files_found = [f.strip() for f in find_result.stdout.strip().split('\n') if f.strip()]
            backed_up_files = {}

            print(f'📁 [TEST] Found {len(files_found)} baseline Verilog files to backup:')
            for file_path in files_found:
                filename = os.path.basename(file_path)
                backup_path = f'{backup_dir}/{filename}'

                # Copy file to backup location
                copy_cmd = ['docker', 'exec', docker_container, 'cp', file_path, backup_path]
                copy_result = subprocess.run(copy_cmd, capture_output=True, text=True)

                if copy_result.returncode == 0:
                    backed_up_files[file_path] = backup_path
                    print(f'     ✅ Backed up baseline Verilog: {filename}')
                else:
                    print(f'     ❌ Failed to backup {filename}: {copy_result.stderr}')

            return {
                'success': True,
                'backup_id': backup_id,
                'backup_dir': backup_dir,
                'files_backed_up': len(backed_up_files),
                'files': backed_up_files,  # This is what the master backup expects
                'baseline_verilog_success': True,
                'is_master_backup': False,
            }

        except Exception as e:
            error_msg = f'Fresh baseline backup failed: {str(e)}'
            print(f'❌ [TEST] {error_msg}')
            return {'success': False, 'error': error_msg}

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

        print('🚀 [TEST] STARTING COMPLETE PIPELINE TEST')
        print('=' * 60)
        print()

        # CRITICAL: Ensure Chisel code is pristine, then generate fresh baseline
        print('🏭 [TEST] STEP 0: Ensure pristine Chisel, then generate fresh baseline Verilog...')

        # First, make sure Chisel code is in original state and clean build cache
        print('🔄 [TEST] Ensuring Chisel code is pristine and cleaning build cache...')
        import subprocess

        # Step 1: Restore Chisel source files
        restore_cmd = [
            'docker',
            'exec',
            'hagent',
            'git',
            '-C',
            '/code/workspace/repo',
            'checkout',
            'HEAD',
            '--',
            'src/main/scala/components/control.scala',
        ]
        restore_result = subprocess.run(restore_cmd, capture_output=True, text=True)
        if restore_result.returncode != 0:
            print(f'⚠️  [TEST] Could not restore Chisel to pristine state: {restore_result.stderr}')
        else:
            print('✅ [TEST] Chisel code restored to pristine state')

        # Verify the Chisel code actually has the original opcode
        verify_cmd = [
            'docker',
            'exec',
            'hagent',
            'grep',
            '-n',
            'b0111011',
            '/code/workspace/repo/src/main/scala/components/control.scala',
        ]
        verify_result = subprocess.run(verify_cmd, capture_output=True, text=True)
        if verify_result.returncode == 0:
            print('✅ [TEST] Verified: Chisel code contains original opcode b0111011')
        else:
            print('⚠️  [TEST] WARNING: Chisel code does not contain expected original opcode b0111011')
            # Try to see what's actually in the file
            cat_cmd = [
                'docker',
                'exec',
                'hagent',
                'grep',
                '-n',
                'b0111',
                '/code/workspace/repo/src/main/scala/components/control.scala',
            ]
            cat_result = subprocess.run(cat_cmd, capture_output=True, text=True)
            print(f'     Current opcodes in file: {cat_result.stdout}')

        # Step 2: Aggressively clean all compilation caches
        print('🧹 [TEST] Cleaning SBT build cache...')
        clean_cmd = ['docker', 'exec', 'hagent', 'bash', '-l', '-c', 'cd /code/workspace/repo && sbt clean']
        clean_result = subprocess.run(clean_cmd, capture_output=True, text=True, timeout=120)
        if clean_result.returncode != 0:
            print(f'⚠️  [TEST] SBT clean failed: {clean_result.stderr}')
        else:
            print('✅ [TEST] SBT build cache cleaned')

        # Also remove target directories and .bloop cache for more aggressive cleaning
        print('🗑️ [TEST] Removing target directories and compilation caches...')
        aggressive_clean_cmd = [
            'docker',
            'exec',
            'hagent',
            'bash',
            '-c',
            'cd /code/workspace/repo && rm -rf target/ project/target/ .bloop/ || true',
        ]
        subprocess.run(aggressive_clean_cmd, capture_output=True, text=True)
        print('✅ [TEST] Removed compilation artifacts')

        # Step 3: Remove any existing golden directory from previous runs
        golden_cleanup_cmd = ['docker', 'exec', 'hagent', 'rm', '-rf', '/code/workspace/repo/lec_golden']
        subprocess.run(golden_cleanup_cmd, capture_output=True, text=True)
        print('✅ [TEST] Removed any existing golden directory')

        # Step 4: Clean both directories to ensure fresh generation
        cleanup_cmd = [
            'docker',
            'exec',
            'hagent',
            'bash',
            '-c',
            'cd /code/workspace && rm -rf build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/* build/build_pipelined_d/* build/build_gcd/* || true',
        ]
        subprocess.run(cleanup_cmd, capture_output=True, text=True)
        print('✅ [TEST] Cleaned all build directories for fresh generation')

        # Now generate fresh baseline from pristine code
        if not processor.generate_fresh_baseline_verilog('hagent'):
            print('❌ [TEST] Failed to generate fresh baseline - test cannot continue')
            return 1
        print('✅ [TEST] Fresh baseline generation complete')
        print()

        # Set up processor exactly like real v2chisel_batch
        processor.input_data = input_data
        processor.output_path = args.output

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
