#!/usr/bin/env python3
"""
Test version of v2chisel_batch that uses Builder API instead of Runner.

This test uses the Builder API to compile Chisel and apply patches,
then uses equivalence checking to validate the results.

Usage:
    uv run python hagent/step/v2chisel_batch/tests/test_v2chisel_batch2.py -o output1.yaml single_adder_test.yaml
"""

import os
import sys
import argparse
from pathlib import Path
from ruamel.yaml import YAML

# Add parent directory to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..')))

from hagent.inou.builder import Builder
from hagent.tool.equiv_check import Equiv_check


def load_input_yaml(input_file):
    """Load input YAML file."""
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
            for i, bug in enumerate(bugs):
                bug_file = bug.get('file', 'unknown')
                print(f'     Bug #{i}: {bug_file}')

        return data

    except Exception as e:
        print(f'❌ [TEST] Error loading input file {input_file}: {e}')
        return None


def apply_verilog_patch_via_runner(runner, file_path, patch_content):
    """Apply a unified diff patch to a Verilog file using runner commands."""
    print(f'🔧 [PATCH] Applying patch to {file_path}')

    try:
        # Write patch content to a local temp file first
        import tempfile

        with tempfile.NamedTemporaryFile(mode='w', suffix='.patch', delete=False) as tmp_file:
            tmp_file.write(patch_content)
            local_patch_file = tmp_file.name

        # Create patch file in container using heredoc (simpler approach)
        container_patch_file = '/tmp/verilog.patch'
        patch_lines = patch_content.split('\n')
        heredoc_content = '\n'.join(patch_lines)
        exit_code, stdout, stderr = runner.run(f"cat <<'EOF' > {container_patch_file}\n{heredoc_content}\nEOF")
        if exit_code != 0:
            print(f'❌ [PATCH] Failed to create patch file in container: {stderr}')
            # Clean up local temp file
            os.unlink(local_patch_file)
            return False

        # Get the directory containing the file
        file_dir = os.path.dirname(file_path)

        # Apply the patch using the patch command
        exit_code, stdout, stderr = runner.run(f'cd {file_dir} && patch -p1 < {container_patch_file}')
        if exit_code != 0:
            print(f'⚠️  [PATCH] Forward patch failed, trying reverse: {stderr}')
            # Sometimes patch direction is reversed, try -R
            exit_code, stdout, stderr = runner.run(f'cd {file_dir} && patch -R -p1 < {container_patch_file}')
            if exit_code != 0:
                print(f'❌ [PATCH] Reverse patch also failed: {stderr}')
                # Clean up temp files
                os.unlink(local_patch_file)
                return False

        print(f'✅ [PATCH] Successfully applied patch to {file_path}')
        # Clean up local temp file
        os.unlink(local_patch_file)
        return True

    except Exception as e:
        print(f'❌ [PATCH] Error applying patch: {e}')
        return False


def apply_chisel_patch_via_runner(runner, repo_path, chisel_diff):
    """Apply the known Chisel diff to control.scala using runner."""
    print('🔧 [CHISEL] Applying Chisel patch to control.scala')

    control_file = f'{repo_path}/src/main/scala/components/control.scala'

    try:
        # Read the original file
        exit_code, original_content, stderr = runner.run(f'cat {control_file}')
        if exit_code != 0:
            print(f'❌ [CHISEL] Failed to read {control_file}: {stderr}')
            return False

        # Apply the known patch manually (simple string replacement)
        # Change BitPat("b0111011") to BitPat("b0111111")
        patched_content = original_content.replace('BitPat("b0111011")', 'BitPat("b0111111")')

        if patched_content != original_content:
            # Write the patched content back using runner with heredoc
            temp_file = '/tmp/control_patched.scala'
            exit_code, stdout, stderr = runner.run(f"cat <<'EOF' > {temp_file}\n{patched_content}\nEOF")
            if exit_code != 0:
                print(f'❌ [CHISEL] Failed to create temp file: {stderr}')
                return False

            # Copy the temp file to the target location
            exit_code, stdout, stderr = runner.run(f'cp {temp_file} {control_file}')
            if exit_code != 0:
                print(f'❌ [CHISEL] Failed to write {control_file}: {stderr}')
                return False

            print(f'✅ [CHISEL] Successfully applied Chisel patch to {control_file}')
            return True
        else:
            print(f'⚠️  [CHISEL] No changes made - pattern not found in {control_file}')
            return False

    except Exception as e:
        print(f'❌ [CHISEL] Error applying Chisel patch: {e}')
        return False


def main():
    """Main function - test v2chisel_batch with Builder API."""

    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description='Test v2chisel_batch with Builder API',
        epilog='Usage: uv run python hagent/step/v2chisel_batch/tests/test_v2chisel_batch2.py -o output1.yaml single_adder_test.yaml',
    )
    parser.add_argument('input_file', help='Input YAML file (e.g., single_adder_test.yaml)')
    parser.add_argument('-o', '--output', required=True, help='Output YAML file')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')

    args = parser.parse_args()

    print('🔬 TEST v2chisel_batch WITH BUILDER API')
    print('=' * 80)
    print('Purpose: Test Chisel compilation and equivalence checking with Builder')
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
    known_chisel_diff = """--- a/components/control.scala
+++ b/components/control.scala
@@ -72,7 +72,7 @@
       // I-format 32-bit operands
       BitPat("b0011011") -> List( true.B,  true.B, false.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
-      // R-format 32-bit operands
-      BitPat("b0111011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
+      // R-format 32-bit operands
+      BitPat("b0111111") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),"""

    builder = None
    try:
        print('🚀 [TEST] STARTING BUILDER API TEST')
        print('=' * 60)
        print()

        # Step 1: Setup builder
        print('🏗️  [TEST] Setting up Builder with Docker image...')
        builder = Builder(docker_image='mascucsc/hagent-simplechisel:2025.11')

        if not builder.setup():
            print(f'❌ [TEST] Failed to setup Builder: {builder.get_error()}')
            return 1

        print('✅ [TEST] Builder setup successful')

        # Step 2: Run compile to check that it works
        print('🔨 [TEST] Running initial compile check...')
        exit_code, stdout, stderr = builder.run_api(exact_name='singlecyclecpu_d', command_name='compile')

        if exit_code != 0:
            print(f'❌ [TEST] Initial compile failed: {stderr}')
            return 1

        print('✅ [TEST] Initial compile successful')

        # Step 3: Create LEC run directory
        print('📁 [TEST] Creating LEC run directory...')
        lec_run_dir = Path('/code/workspace/cache/lec_run')

        # Create directory using Builder's runner
        exit_code, stdout, stderr = builder.runner.run(f'mkdir -p {lec_run_dir}')
        if exit_code != 0:
            print(f'❌ [TEST] Failed to create LEC run directory: {stderr}')
            return 1

        print(f'✅ [TEST] Created LEC run directory: {lec_run_dir}')

        # Step 4: Process bugs from input YAML
        bugs = input_data.get('bugs', [])
        if not bugs:
            print('❌ [TEST] No bugs found in input file')
            return 1

        print(f'🐛 [TEST] Processing {len(bugs)} bugs...')

        results = []

        for i, bug in enumerate(bugs):
            bug_name = f'bug{i}'
            bug_file = bug.get('file', 'unknown.sv')
            patch_content = bug.get('unified_diff', '')

            print(f'\n--- Processing {bug_name}: {bug_file} ---')

            # Create bug subdirectory
            bug_dir = lec_run_dir / bug_name
            exit_code, stdout, stderr = builder.runner.run(f'mkdir -p {bug_dir}')
            if exit_code != 0:
                print(f'❌ [TEST] Failed to create bug directory: {stderr}')
                continue

            # Copy original file to LEC run directory
            source_file = f'/code/workspace/build/build_singlecyclecpu_d/{bug_file}'
            target_file = bug_dir / bug_file

            exit_code, stdout, stderr = builder.runner.run(f'cp {source_file} {target_file}')
            if exit_code != 0:
                print(f'❌ [TEST] Failed to copy {bug_file}: {stderr}')
                continue

            print(f'✅ [TEST] Copied {bug_file} to {bug_dir}')

            # Apply bug patch to original build file
            if patch_content:
                if not apply_verilog_patch_via_runner(builder.runner, source_file, patch_content):
                    print(f'❌ [TEST] Failed to apply patch to {source_file}')
                    continue

            # Create Equiv_check object and run equivalence check
            print(f'🔍 [TEST] Running equivalence check for {bug_name}...')

            try:
                checker = Equiv_check()
                if not checker.setup():
                    print(f'❌ [TEST] Equiv_check setup failed: {checker.get_error()}')
                    continue

                # Read both files for comparison
                exit_code, original_content, stderr = builder.runner.run(f'cat {target_file}')
                if exit_code != 0:
                    print(f'❌ [TEST] Failed to read original file: {stderr}')
                    continue

                exit_code, patched_content, stderr = builder.runner.run(f'cat {source_file}')
                if exit_code != 0:
                    print(f'❌ [TEST] Failed to read patched file: {stderr}')
                    continue

                # Run equivalence check
                result = checker.check_equivalence(original_content, patched_content)

                if result is False:
                    print(f'✅ [TEST] Expected result: {bug_name} files are NOT equivalent (as expected)')
                    results.append({'bug': bug_name, 'file': bug_file, 'equiv_check': 'not_equivalent_as_expected'})
                elif result is True:
                    print(f'⚠️  [TEST] Unexpected: {bug_name} files are equivalent')
                    results.append({'bug': bug_name, 'file': bug_file, 'equiv_check': 'unexpected_equivalent'})
                else:
                    print(f'❌ [TEST] Equivalence check inconclusive for {bug_name}')
                    results.append({'bug': bug_name, 'file': bug_file, 'equiv_check': 'inconclusive'})

            except Exception as e:
                print(f'❌ [TEST] Exception during equivalence check: {e}')
                results.append({'bug': bug_name, 'file': bug_file, 'equiv_check': f'error: {e}'})

        # Step 5: Apply known Chisel diff and recompile
        print('\n🔧 [TEST] Applying known Chisel diff and recompiling...')

        # Apply the Chisel patch
        repo_path = '/code/workspace/repo'
        if apply_chisel_patch_via_runner(builder.runner, repo_path, known_chisel_diff):
            # Recompile with the patch
            print('🔨 [TEST] Recompiling with Chisel patch...')
            exit_code, stdout, stderr = builder.run_api(exact_name='singlecyclecpu_d', command_name='compile')

            if exit_code == 0:
                print('✅ [TEST] Recompile with Chisel patch successful')

                # Step 6: Run final equivalence check
                print('🔍 [TEST] Running final equivalence check...')

                try:
                    # Check the first bug (bug0) with the new compiled version
                    if bugs:
                        bug_file = bugs[0].get('file', 'Control.sv')
                        original_file = lec_run_dir / 'bug0' / bug_file
                        new_compiled_file = f'/code/workspace/build/build_singlecyclecpu_d/{bug_file}'

                        checker = Equiv_check()
                        if checker.setup():
                            # Read both files
                            exit_code, original_content, stderr = builder.runner.run(f'cat {original_file}')
                            exit_code2, new_content, stderr2 = builder.runner.run(f'cat {new_compiled_file}')

                            if exit_code == 0 and exit_code2 == 0:
                                final_result = checker.check_equivalence(original_content, new_content)

                                if final_result is True:
                                    print('🎉 [TEST] SUCCESS: Files are now equivalent after Chisel patch!')
                                    results.append({'final_check': 'equivalent_after_chisel_patch'})
                                elif final_result is False:
                                    print('⚠️  [TEST] Files are still not equivalent after Chisel patch')
                                    results.append({'final_check': 'still_not_equivalent'})
                                else:
                                    print('❌ [TEST] Final equivalence check inconclusive')
                                    results.append({'final_check': 'inconclusive'})
                            else:
                                print('❌ [TEST] Failed to read files for final check')
                                results.append({'final_check': 'file_read_error'})
                        else:
                            print(f'❌ [TEST] Final equiv_check setup failed: {checker.get_error()}')
                            results.append({'final_check': 'setup_error'})

                except Exception as e:
                    print(f'❌ [TEST] Exception during final check: {e}')
                    results.append({'final_check': f'error: {e}'})

            else:
                print(f'❌ [TEST] Recompile with Chisel patch failed: {stderr}')
                results.append({'recompile': 'failed'})
        else:
            print('❌ [TEST] Failed to apply Chisel patch')
            results.append({'chisel_patch': 'failed'})

        # Save results
        print(f'\n📊 [TEST] Saving results to {args.output}...')
        output_data = {
            'test_type': 'builder_api_test',
            'input_file': args.input_file,
            'bugs_processed': len(bugs),
            'results': results,
        }

        yaml = YAML()
        with open(args.output, 'w') as f:
            yaml.dump(output_data, f)

        print('✅ [TEST] Results saved')
        print()
        print('=' * 60)
        print('🎉 [TEST] BUILDER API TEST COMPLETED!')
        print(f'Processed {len(bugs)} bugs with Builder API')
        print(f'Results saved to: {args.output}')
        print('=' * 60)

        return 0

    except Exception as e:
        print(f'💥 [TEST] EXCEPTION: {str(e)}')
        if args.debug:
            import traceback

            traceback.print_exc()
        return 1

    finally:
        # Cleanup
        if builder:
            try:
                print('🧹 [TEST] Cleaning up Builder...')
                builder.cleanup()
            except Exception as cleanup_error:
                print(f'⚠️ [TEST] Cleanup warning: {cleanup_error}')


if __name__ == '__main__':
    # Docker mode enabled via HAGENT_DOCKER
    exit_code = main()
    print()
    print('=' * 80)
    if exit_code == 0:
        print('🎉 TEST COMPLETED SUCCESSFULLY!')
    else:
        print('💥 TEST FAILED!')
    print('=' * 80)
    sys.exit(exit_code)
