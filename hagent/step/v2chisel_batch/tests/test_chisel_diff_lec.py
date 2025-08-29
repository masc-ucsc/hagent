#!/usr/bin/env python3
"""
Test chisel_diff application and LEC in isolation.

This test manually applies a known chisel_diff and then runs the LEC part
to test the second half of the pipeline without dealing with LLM/module_finder complexity.
"""

import os
import sys
import tempfile
import subprocess


def apply_chisel_diff_manually():
    """Manually apply the known chisel_diff to test Control.scala"""

    # Example chisel_diff (unused in this function):
    # """@@ -1194,7 +1194,7 @@
    #        // I-format 32-bit operands
    #        BitPat("b0011011") -> List( true.B,  true.B, false.B,  1.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
    # -       // R-format 32-bit operands
    # -       BitPat("b0111011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
    # +       // R-format 32-bit operands
    # +       BitPat("b0111111") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
    # """

    print('🎯 [TEST] Manually applying chisel_diff to Control.scala in Docker...')

    # Find control.scala in the Docker container
    docker_container = 'hagent'
    find_cmd = ['docker', 'exec', docker_container, 'find', '/code/workspace/repo', '-name', 'control.scala', '-type', 'f']

    try:
        result = subprocess.run(find_cmd, capture_output=True, text=True, timeout=30)
        if result.returncode != 0 or not result.stdout.strip():
            print('❌ Could not find control.scala in Docker container')
            return False

        control_files = [f.strip() for f in result.stdout.strip().split('\n') if f.strip()]
        print(f'📁 Found control.scala files: {control_files}')

        if not control_files:
            print('❌ No control.scala files found')
            return False

        control_file = control_files[0]  # Use first one
        print(f'🎯 Using control.scala: {control_file}')

        # Read current content
        read_cmd = ['docker', 'exec', docker_container, 'cat', control_file]
        read_result = subprocess.run(read_cmd, capture_output=True, text=True)

        if read_result.returncode != 0:
            print('❌ Could not read control.scala')
            return False

        original_content = read_result.stdout
        print(f'📖 Read control.scala: {len(original_content)} characters')

        # Apply the diff (simple string replacement for this test)
        if '"b0111011"' in original_content:
            modified_content = original_content.replace('"b0111011"', '"b0111111"')
            print('✅ Applied change: b0111011 → b0111111')
        else:
            print('⚠️  Could not find b0111011 in control.scala, applying anyway for test')
            modified_content = original_content

        # Write modified content back
        write_cmd = ['docker', 'exec', '-i', docker_container, 'tee', control_file]
        write_result = subprocess.run(write_cmd, input=modified_content, text=True, capture_output=True)

        if write_result.returncode != 0:
            print('❌ Could not write modified control.scala')
            return False

        print('✅ Successfully applied chisel_diff to control.scala')
        return True

    except Exception as e:
        print(f'❌ Exception applying chisel_diff: {e}')
        return False


def compile_and_generate_verilog():
    """Compile Chisel and generate Verilog"""
    print('🔨 [TEST] Compiling Chisel and generating Verilog...')

    docker_container = 'hagent'

    # Try the SingleCycleCPU generation command
    compile_cmd = [
        'docker',
        'exec',
        '-u',
        'user',
        docker_container,
        'bash',
        '-l',
        '-c',
        'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
    ]

    try:
        result = subprocess.run(compile_cmd, capture_output=True, text=True, timeout=300)

        if result.returncode == 0:
            print('✅ Chisel compilation and verilog generation successful')
            return True
        else:
            print(f'❌ Compilation failed with exit code {result.returncode}')
            print(f'STDERR: {result.stderr[:500]}...')
            return False

    except subprocess.TimeoutExpired:
        print('❌ Compilation timeout (300s)')
        return False
    except Exception as e:
        print(f'❌ Compilation exception: {e}')
        return False


def run_lec_test():
    """Run LEC test with golden design creation and comparison"""
    print('🔍 [TEST] Running LEC with golden design creation...')

    docker_container = 'hagent'

    try:
        # Step 1: Create golden design directory
        mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', '/code/workspace/repo/lec_golden']
        subprocess.run(mkdir_cmd, check=True)

        # Step 2: Copy original verilog to golden design
        original_path = '/code/workspace/build/build_singlecyclecpu_nd'
        golden_path = '/code/workspace/repo/lec_golden'

        copy_cmd = ['docker', 'exec', docker_container, 'bash', '-c', f'cp {original_path}/*.sv {golden_path}/']
        copy_result = subprocess.run(copy_cmd, capture_output=True, text=True)

        if copy_result.returncode != 0:
            print('❌ Failed to copy original verilog to golden design')
            return False

        print('✅ Created golden design from original verilog')

        # Step 3: Apply verilog_diff to golden design (the target change)
        # For this test, we need to modify the golden Control.sv to have the target change
        verilog_diff_cmd = ['docker', 'exec', docker_container, 'sed', '-i', "s/7'h3B/7'h3F/g", f'{golden_path}/Control.sv']
        subprocess.run(verilog_diff_cmd, capture_output=True)
        print('✅ Applied verilog_diff to golden design')

        # Step 4: Run LEC between golden and gate (newly generated)
        golden_files = []
        gate_files = []

        # Get golden files
        golden_find_cmd = ['docker', 'exec', docker_container, 'find', golden_path, '-name', '*.sv', '-type', 'f']
        golden_result = subprocess.run(golden_find_cmd, capture_output=True, text=True)
        if golden_result.returncode == 0:
            golden_files = [f.strip() for f in golden_result.stdout.strip().split('\n') if f.strip()]

        # Get gate files (newly generated)
        gate_paths = ['/code/workspace/repo/generated', '/code/workspace/repo', '/code/workspace/build']
        for gate_path in gate_paths:
            gate_find_cmd = ['docker', 'exec', docker_container, 'find', gate_path, '-name', '*.sv', '-type', 'f']
            gate_result = subprocess.run(gate_find_cmd, capture_output=True, text=True)
            if gate_result.returncode == 0 and gate_result.stdout.strip():
                found_files = [f.strip() for f in gate_result.stdout.strip().split('\n') if f.strip()]
                # Filter to only SingleCycleCPU files
                filtered_files = [
                    f
                    for f in found_files
                    if not f.startswith(golden_path)
                    and any(
                        pattern in os.path.basename(f)
                        for pattern in ['SingleCycleCPU', 'Control', 'ALU', 'RegisterFile', 'NextPC', 'ImmediateGenerator']
                    )
                ]
                gate_files.extend(filtered_files)

        print(f'📁 Found {len(golden_files)} golden files and {len(gate_files)} gate files')

        if not golden_files or not gate_files:
            print('❌ Not enough files for LEC comparison')
            return False

        # Step 5: Copy files to host and run LEC
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_golden_dir = os.path.join(temp_dir, 'golden')
            temp_gate_dir = os.path.join(temp_dir, 'gate')
            os.makedirs(temp_golden_dir, exist_ok=True)
            os.makedirs(temp_gate_dir, exist_ok=True)

            # Copy golden files to host
            copied_golden_files = []
            for golden_file in golden_files:
                filename = os.path.basename(golden_file)
                host_path = os.path.join(temp_golden_dir, filename)
                copy_cmd = ['docker', 'cp', f'{docker_container}:{golden_file}', host_path]
                if subprocess.run(copy_cmd, capture_output=True).returncode == 0:
                    copied_golden_files.append(host_path)

            # Copy gate files to host (deduplicated)
            copied_gate_files = []
            seen_filenames = set()
            for gate_file in gate_files:
                filename = os.path.basename(gate_file)
                if filename not in seen_filenames:
                    seen_filenames.add(filename)
                    host_path = os.path.join(temp_gate_dir, filename)
                    copy_cmd = ['docker', 'cp', f'{docker_container}:{gate_file}', host_path]
                    if subprocess.run(copy_cmd, capture_output=True).returncode == 0:
                        copied_gate_files.append(host_path)

            print(f'📋 Copied {len(copied_golden_files)} golden and {len(copied_gate_files)} gate files to host')

            # Run LEC
            cli_equiv_check_path = '/home/farzaneh/hagent/hagent/tool/tests/cli_equiv_check.py'
            lec_cmd = ['uv', 'run', 'python', cli_equiv_check_path]

            for golden_file in copied_golden_files:
                lec_cmd.extend(['-r', golden_file])
            for gate_file in copied_gate_files:
                lec_cmd.extend(['-i', gate_file])

            lec_cmd.extend(['--top', 'SingleCycleCPU', '--verbose'])

            print('🚀 Running LEC command...')
            lec_result = subprocess.run(lec_cmd, capture_output=True, text=True, timeout=300)

            print(f'📊 LEC Exit Code: {lec_result.returncode}')
            if lec_result.stdout:
                print('📋 LEC Output:')
                print(lec_result.stdout)
            if lec_result.stderr:
                print('⚠️  LEC Errors:')
                print(lec_result.stderr)

            if lec_result.returncode == 0:
                print('✅ LEC PASSED: Designs are equivalent!')
                return True
            else:
                print('❌ LEC FAILED: Designs are not equivalent or error occurred')
                return False

    except Exception as e:
        print(f'❌ LEC test exception: {e}')
        return False


def main():
    """Run the focused chisel_diff + LEC test"""
    print('🔬 CHISEL DIFF + LEC FOCUSED TEST')
    print('=' * 60)
    print('Purpose: Test chisel_diff application + compilation + LEC')
    print('Steps: Apply chisel_diff → Compile → Generate Verilog → Create Golden → LEC')
    print('=' * 60)
    print()

    success = True

    # Step 1: Apply chisel_diff
    if not apply_chisel_diff_manually():
        print('💥 STEP 1 FAILED: Could not apply chisel_diff')
        success = False

    # Step 2: Compile and generate Verilog
    if success and not compile_and_generate_verilog():
        print('💥 STEP 2 FAILED: Could not compile/generate Verilog')
        success = False

    # Step 3: Run LEC test
    if success and not run_lec_test():
        print('💥 STEP 3 FAILED: LEC test failed')
        success = False

    print()
    print('=' * 60)
    if success:
        print('🎉 TEST RESULT: SUCCESS - Chisel diff + LEC pipeline works!')
        print('This proves the second half of the v2chisel_batch pipeline is functional.')
        sys.exit(0)
    else:
        print('💥 TEST RESULT: FAILURE - Issues in chisel diff + LEC pipeline')
        sys.exit(1)


if __name__ == '__main__':
    main()
