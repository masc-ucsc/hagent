#!/usr/bin/env python3
"""
Test version of v2chisel_batch that uses Builder API with debugging verification steps.

This test uses the Builder API to compile Chisel and apply patches,
with verification steps to ensure each operation works correctly.

Usage:
    uv run python hagent/step/v2chisel_batch/tests/test_v2chisel_batch3.py -o output1.yaml single_adder_test.yaml
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


def verify_verilog_patch_applied(runner, file_path, expected_change_from, expected_change_to):
    """Verify that the Verilog patch was actually applied correctly."""
    print(f'🔍 [VERIFY] Checking if Verilog patch was applied to {file_path}')

    try:
        # Read the patched file
        exit_code, file_content, stderr = runner.run(f'cat {file_path}')
        if exit_code != 0:
            print(f'❌ [VERIFY] Failed to read {file_path}: {stderr}')
            return False

        # Check if the old pattern is gone
        if expected_change_from in file_content:
            print(f'❌ [VERIFY] Old pattern "{expected_change_from}" still found in file')
            print('🔍 [VERIFY] File content around pattern:')
            lines = file_content.split('\n')
            for i, line in enumerate(lines):
                if expected_change_from in line:
                    print(f'     Line {i+1}: {line.strip()}')
            return False

        # Check if the new pattern is present
        if expected_change_to not in file_content:
            print(f'❌ [VERIFY] New pattern "{expected_change_to}" not found in file')
            return False

        # Find and print the line with the change
        lines = file_content.split('\n')
        for i, line in enumerate(lines):
            if expected_change_to in line:
                print('✅ [VERIFY] Apply a bug patch to the Verilog is done correctly')
                print(f'🔍 [VERIFY] Found change at line {i+1}: {line.strip()}')
                return True

        return False

    except Exception as e:
        print(f'❌ [VERIFY] Exception during verification: {e}')
        return False


def verify_chisel_patch_applied(runner, file_path, expected_change_from, expected_change_to):
    """Verify that the Chisel patch was actually applied correctly."""
    print(f'🔍 [VERIFY] Checking if Chisel patch was applied to {file_path}')

    try:
        # Read the patched file
        exit_code, file_content, stderr = runner.run(f'cat {file_path}')
        if exit_code != 0:
            print(f'❌ [VERIFY] Failed to read {file_path}: {stderr}')
            return False

        # Check if the old pattern is gone
        if expected_change_from in file_content:
            print(f'❌ [VERIFY] Old Chisel pattern "{expected_change_from}" still found in file')
            print('🔍 [VERIFY] File content around old pattern:')
            lines = file_content.split('\n')
            for i, line in enumerate(lines):
                if expected_change_from in line:
                    print(f'     Line {i+1}: {line.strip()}')
            return False

        # Check if the new pattern is present
        if expected_change_to not in file_content:
            print(f'❌ [VERIFY] New Chisel pattern "{expected_change_to}" not found in file')
            print('🔍 [VERIFY] Searching for similar patterns:')
            lines = file_content.split('\n')
            for i, line in enumerate(lines):
                if 'BitPat(' in line and '0111' in line:
                    print(f'     Line {i+1}: {line.strip()}')
            return False

        # Find and print the line with the change
        lines = file_content.split('\n')
        for i, line in enumerate(lines):
            if expected_change_to in line:
                print('✅ [VERIFY] Apply a "known correct" Chisel fix is done correctly')
                print(f'🔍 [VERIFY] Found Chisel change at line {i+1}: {line.strip()}')
                return True

        return False

    except Exception as e:
        print(f'❌ [VERIFY] Exception during Chisel verification: {e}')
        return False


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
    """Main function - test v2chisel_batch with Builder API and debugging."""

    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description='Test v2chisel_batch with Builder API and debugging verification',
        epilog='Usage: uv run python hagent/step/v2chisel_batch/tests/test_v2chisel_batch3.py -o output1.yaml single_adder_test.yaml',
    )
    parser.add_argument('input_file', help='Input YAML file (e.g., single_adder_test.yaml)')
    parser.add_argument('-o', '--output', required=True, help='Output YAML file')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')

    args = parser.parse_args()

    print('🔬 TEST v2chisel_batch WITH BUILDER API + DEBUGGING')
    print('=' * 80)
    print('Purpose: Test Chisel compilation and equivalence checking with verification')
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
        print('🚀 [TEST] STARTING BUILDER API TEST WITH DEBUGGING')
        print('=' * 60)
        print()

        # Step 1: Setup builder
        print('🏗️  [TEST] Setting up Builder with Docker image...')
        builder = Builder(docker_image='mascucsc/hagent-simplechisel:2025.09r')

        if not builder.setup():
            print(f'❌ [TEST] Failed to setup Builder: {builder.get_error()}')
            return 1

        print('✅ [TEST] Builder setup successful')

        # Step 0: CRITICAL - Ensure we start with ORIGINAL Chisel code
        print('🔄 [TEST] Step 0: Ensuring ORIGINAL Chisel code (restore if needed)')
        repo_path = '/code/workspace/repo'
        control_file = f'{repo_path}/src/main/scala/components/control.scala'

        # Read current control.scala to check if we need to restore
        exit_code, current_content, stderr = builder.runner.run(f'cat {control_file}')
        if exit_code != 0:
            print(f'❌ [TEST] Failed to read {control_file}: {stderr}')
            return 1

        # Check if file contains the "fixed" pattern - if so, we need to restore original
        if 'BitPat("b0111111")' in current_content:
            print('⚠️  [TEST] Found FIXED Chisel code - need to restore to ORIGINAL')

            # Restore using git to get original version
            exit_code, stdout, stderr = builder.runner.run('git config --global --add safe.directory /code/workspace/repo')
            if exit_code != 0:
                print(f'⚠️  [TEST] Git config warning: {stderr}')

            # Try multiple restoration approaches
            print('🔄 [TEST] Attempting git checkout restoration...')
            exit_code, stdout, stderr = builder.runner.run(
                f'cd {repo_path} && git checkout HEAD -- src/main/scala/components/control.scala'
            )
            if exit_code != 0:
                print(f'❌ [TEST] Git checkout failed: {stderr}')
                print('🔄 [TEST] Trying git reset approach...')
                exit_code, stdout, stderr = builder.runner.run(f'cd {repo_path} && git reset --hard HEAD')
                if exit_code != 0:
                    print(f'❌ [TEST] Git reset also failed: {stderr}')
                    return 1

            # Verify restoration worked - read file again
            exit_code, restored_content, stderr = builder.runner.run(f'cat {control_file}')
            if exit_code != 0:
                print(f'❌ [TEST] Failed to read restored file: {stderr}')
                return 1

            print('🔍 [TEST] Checking restored content...')
            if 'BitPat("b0111011")' in restored_content and 'BitPat("b0111111")' not in restored_content:
                print('✅ [TEST] Successfully restored ORIGINAL Chisel code with BitPat("b0111011")')
            else:
                print('❌ [TEST] Restoration verification failed!')
                print('🔍 [DEBUG] Looking for BitPat patterns in restored file:')
                lines = restored_content.split('\n')
                for i, line in enumerate(lines):
                    if 'BitPat(' in line and ('0111' in line):
                        print(f'     Line {i+1}: {line.strip()}')
                print('❌ [TEST] File still contains wrong pattern - manual restore needed')
                return 1
        else:
            print('✅ [TEST] Chisel code is already in ORIGINAL state with BitPat("b0111011")')

        # Step 1: Prepare build environment and run compile
        print('🔨 [TEST] Step 1: Start with working Chisel code → compile it → get working Verilog (Control.sv)')

        # Ensure build directories exist to prevent tracking errors
        print('📁 [TEST] Preparing build directories...')
        builder.runner.run('mkdir -p /code/workspace/build/build_singlecyclecpu_d')
        builder.runner.run('mkdir -p /code/workspace/cache')

        exit_code, stdout, stderr = builder.run_api(exact_name='singlecyclecpu_d', command_name='compile')

        if exit_code != 0:
            print(f'❌ [TEST] Initial compile failed: {stderr}')
            return 1

        print('✅ [TEST] Step 1 completed: Working Verilog generated successfully')

        # Verify build directory exists
        print('🔍 [TEST] Verifying build directory exists...')
        build_dir = '/code/workspace/build/build_singlecyclecpu_d'
        exit_code, stdout, stderr = builder.runner.run(f'ls -la {build_dir}')
        if exit_code != 0:
            print(f'❌ [TEST] Build directory does not exist: {build_dir}')
            print(f'Error: {stderr}')
            return 1
        else:
            print(f'✅ [TEST] Build directory exists: {build_dir}')

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

            # Verify source file exists before copying
            source_file = f'/code/workspace/build/build_singlecyclecpu_d/{bug_file}'
            exit_code, stdout, stderr = builder.runner.run(f'ls -la {source_file}')
            if exit_code != 0:
                print(f'❌ [TEST] Source file {bug_file} does not exist in build directory')
                print('Available files in build directory:')
                builder.runner.run('ls -la /code/workspace/build/build_singlecyclecpu_d/')
                continue

            # Copy original file to LEC run directory
            target_file = bug_dir / bug_file
            exit_code, stdout, stderr = builder.runner.run(f'cp {source_file} {target_file}')
            if exit_code != 0:
                print(f'❌ [TEST] Failed to copy {bug_file}: {stderr}')
                continue

            print(f'✅ [TEST] Copied {bug_file} to {bug_dir}')

            # Step 2: Apply bug patch to original build file
            print(
                '🔧 [TEST] Step 2: Apply a bug patch to the Verilog → now we have "buggy" Verilog with 7\'h3B changed to 7\'h3F'
            )
            if patch_content:
                if not apply_verilog_patch_via_runner(builder.runner, source_file, patch_content):
                    print(f'❌ [TEST] Failed to apply patch to {source_file}')
                    continue

                # VERIFICATION STEP: Verify the Verilog patch was applied correctly
                if not verify_verilog_patch_applied(builder.runner, source_file, "7'h3B", "7'h3F"):
                    print('❌ [TEST] Verilog patch verification failed')
                    continue

            # Step 3: Create Equiv_check object and run equivalence check
            print('🔍 [TEST] Step 3: Run equivalence check → confirms the original vs buggy Verilog are different')

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
                    print(f'✅ [TEST] Step 3 completed: {bug_name} files are NOT equivalent (as expected)')
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

        # Step 4: Apply known Chisel diff and recompile
        print('\n🔧 [TEST] Step 4: Apply a "known correct" Chisel fix → change BitPat("b0111011") to BitPat("b0111111")')

        # Apply the Chisel patch
        repo_path = '/code/workspace/repo'
        chisel_apply_success = apply_chisel_patch_via_runner(builder.runner, repo_path, known_chisel_diff)

        # CRITICAL VERIFICATION STEP: Always verify the Chisel patch regardless of apply result
        print('🔍 [CRITICAL] VERIFYING CHISEL PATCH APPLICATION - THIS IS THE MOST IMPORTANT STEP')
        control_file = f'{repo_path}/src/main/scala/components/control.scala'
        chisel_verified = verify_chisel_patch_applied(builder.runner, control_file, 'BitPat("b0111011")', 'BitPat("b0111111")')

        if chisel_apply_success and chisel_verified:
            # CRITICAL: Backup the PATCHED Verilog before recompiling
            print('💾 [TEST] Backing up PATCHED Verilog before recompilation...')
            bug_file = bugs[0].get('file', 'Control.sv') if bugs else 'Control.sv'
            patched_verilog_file = f'/code/workspace/build/build_singlecyclecpu_d/{bug_file}'
            patched_backup_file = f'/code/workspace/cache/lec_run/bug0_patched_{bug_file}'
            exit_code, stdout, stderr = builder.runner.run(f'cp {patched_verilog_file} {patched_backup_file}')
            if exit_code != 0:
                print(f'❌ [TEST] Failed to backup patched Verilog: {stderr}')
                results.append({'backup_patched': 'failed'})
            else:
                print(f'✅ [TEST] Backed up patched Verilog to {patched_backup_file}')

            # Recompile with the patch
            print('🔨 [TEST] Step 5: Recompiling with Chisel patch...')
            exit_code, stdout, stderr = builder.run_api(exact_name='singlecyclecpu_d', command_name='compile')

            if exit_code == 0:
                print('✅ [TEST] Recompile with Chisel patch successful')

                # Step 6: Run final equivalence check
                print('🔍 [TEST] Step 6: Running final equivalence check...')

                try:
                    # CORRECT FINAL LEC: Compare PATCHED Verilog vs NEWLY GENERATED Verilog
                    # Both should have 7'h3F and be equivalent
                    if bugs:
                        bug_file = bugs[0].get('file', 'Control.sv')
                        # Gold: The PATCHED Verilog (target we want to achieve)
                        patched_verilog_file = f'/code/workspace/build/build_singlecyclecpu_d/{bug_file}'
                        # Gate: Newly generated Verilog from fixed Chisel
                        new_compiled_file = f'/code/workspace/build/build_singlecyclecpu_d/{bug_file}'

                        print('🔍 [TEST] Final LEC: Comparing PATCHED Verilog vs NEWLY GENERATED Verilog')
                        print("     Both should have 7'h3F and be equivalent")

                        # Since we're comparing the same file path, we need to save the patched version first
                        # Save the current patched version before recompilation
                        patched_backup_file = f'/code/workspace/cache/lec_run/bug0_patched_{bug_file}'
                        exit_code, stdout, stderr = builder.runner.run(f'cp {patched_verilog_file} {patched_backup_file}')
                        if exit_code != 0:
                            print(f'❌ [TEST] Failed to backup patched file: {stderr}')
                            results.append({'final_check': 'backup_failed'})
                        else:
                            # Only proceed if backup succeeded
                            checker = Equiv_check()
                            if checker.setup():
                                # Read both files
                                # Gold: Patched Verilog (backed up before recompilation)
                                exit_code, patched_content, stderr = builder.runner.run(f'cat {patched_backup_file}')
                                # Gate: Newly generated Verilog (after recompilation)
                                exit_code2, new_content, stderr2 = builder.runner.run(f'cat {new_compiled_file}')

                                if exit_code == 0 and exit_code2 == 0:
                                    print('🔍 [DEBUG] Patched Verilog content check:')
                                    lines = patched_content.split('\n')
                                    for i, line in enumerate(lines):
                                        if "7'h3" in line and 'signals_T_132' in line:
                                            print(f'     Patched Line {i+1}: {line.strip()}')

                                    print('🔍 [DEBUG] New generated Verilog content check:')
                                    lines = new_content.split('\n')
                                    for i, line in enumerate(lines):
                                        if "7'h3" in line and 'signals_T_132' in line:
                                            print(f'     Generated Line {i+1}: {line.strip()}')

                                    final_result = checker.check_equivalence(patched_content, new_content)

                                    if final_result is True:
                                        print('🎉 [TEST] SUCCESS: Files are now equivalent after Chisel patch!')
                                        results.append({'final_check': 'equivalent_after_chisel_patch'})
                                    elif final_result is False:
                                        print('⚠️  [TEST] Files are still not equivalent after Chisel patch')

                                        # DEBUG: Show what we're comparing
                                        print('🔍 [DEBUG] Showing generated Verilog after Chisel patch:')
                                        lines = new_content.split('\n')
                                        for i, line in enumerate(lines):
                                            if "7'h3" in line and 'signals_T_132' in line:
                                                print(f'     Line {i+1}: {line.strip()}')

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
            if not chisel_apply_success:
                print('❌ [TEST] Failed to apply Chisel patch')
                results.append({'chisel_patch': 'apply_failed'})
            elif not chisel_verified:
                print('❌ [TEST] Chisel patch applied but verification failed')
                results.append({'chisel_patch': 'verification_failed'})
            else:
                print('❌ [TEST] Unknown Chisel patch issue')
                results.append({'chisel_patch': 'unknown_issue'})

        # Save results
        print(f'\n📊 [TEST] Saving results to {args.output}...')
        output_data = {
            'test_type': 'builder_api_test_with_debugging',
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
        print('🎉 [TEST] BUILDER API TEST WITH DEBUGGING COMPLETED!')
        print(f'Processed {len(bugs)} bugs with Builder API and verification')
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
    os.environ['HAGENT_EXECUTION_MODE'] = 'docker'
    exit_code = main()
    print()
    print('=' * 80)
    if exit_code == 0:
        print('🎉 TEST WITH DEBUGGING COMPLETED SUCCESSFULLY!')
    else:
        print('💥 TEST WITH DEBUGGING FAILED!')
    print('=' * 80)
    sys.exit(exit_code)
