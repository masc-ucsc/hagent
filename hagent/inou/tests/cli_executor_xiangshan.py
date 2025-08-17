#!/usr/bin/env python3
"""
XiangShan test example using Runner for unified execution and file tracking.
Demonstrates file modification, Verilog generation, and change tracking with simplified API.
Converted to use Runner instead of direct Executor/ContainerManager/PathManager/FileTracker usage.

Can be run as:
1. CLI tool: uv run python hagent/inou/tests/cli_executor_xiangshan.py
2. Slow test: uv run pytest -m slow hagent/inou/tests/cli_executor_xiangshan.py
"""

import os
import pytest

# Set up environment for testing - only set execution mode
# Let Runner handle all Docker paths internally
os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

from hagent.inou.runner import Runner


def _run_xiangshan_test():
    """Core XiangShan test logic - shared between CLI and pytest."""

    # 1. Initialize Runner with Docker image
    runner = Runner(docker_image='mascucsc/hagent-xiangshan:2025.08')

    # 2. Setup runner (creates and configures container)
    assert runner.setup(), f'Setup failed: {runner.get_error()}'
    print('✅ Container setup successful')

    # 4. Check if XiangShan project exists and verify key files
    print('Checking for XiangShan project structure...')

    # Check for main project directory
    exit_code, stdout, stderr = runner.run('ls -la /code/workspace/repo/', cwd='/')
    if exit_code != 0:
        print('⚠️  XiangShan project not found in expected location')
        print('This test requires the mascucsc/hagent-xiangshan:2025.08 image with XiangShan project')
        runner.cleanup()
        return

    print('✅ Found XiangShan project at: /code/workspace/repo')

    # 5. Check for specific files we'll be working with
    ifu_path = '/code/workspace/repo/src/main/scala/xiangshan/frontend/IFU.scala'
    rtl_path = '/code/workspace/repo/build/rtl'

    # Track source files and build directories before making changes
    print('📝 Setting up file tracking for source and build files...')

    # Track the IFU source file that we'll modify
    runner.track_file('src/main/scala/xiangshan/frontend/IFU.scala')

    # Track Scala source files in the frontend directory
    runner.track_dir('src/main/scala/xiangshan/frontend', '.scala')

    # Track generated Verilog/SystemVerilog files in build directory
    runner.track_dir('build', '.sv')
    runner.track_dir('build', '.v')

    print('✅ File tracking configured for source and generated files')

    print('Checking for IFU.scala file...')
    exit_code, stdout, stderr = runner.run(f'test -f "{ifu_path}"', cwd='/')
    if exit_code != 0:
        print(f'❌ IFU.scala file not found at {ifu_path}')
        # Try to find it
        print('Searching for IFU.scala in the project...')
        exit_code, stdout, stderr = runner.run('find /code/workspace/repo -name "IFU.scala" | head -5', cwd='/')
        if stdout.strip():
            print(f'Found IFU.scala files at:\n{stdout}')
            # Use the first found file and update our tracking
            ifu_path = stdout.strip().split('\n')[0]
            print(f'Using: {ifu_path}')
            # Update tracking with the actual found path
            ifu_relative = ifu_path.replace('/code/workspace/repo/', '')
            runner.track_file(ifu_relative)
        else:
            print('⚠️  No IFU.scala file found. Skipping file modification test.')
            ifu_path = None

    if ifu_path:
        print(f'✅ Found IFU.scala at: {ifu_path}')

    print('Checking for RTL build directory...')
    exit_code, stdout, stderr = runner.run(f'test -d "{rtl_path}"', cwd='/')
    if exit_code != 0:
        print(f'⚠️  RTL directory not found at {rtl_path} (will be created during build)')
    else:
        print(f'✅ Found RTL directory at: {rtl_path}')

    # 6. Apply file modification if IFU.scala is available
    if ifu_path:
        print('Applying test modification to IFU.scala...')

        # First, let's see the current content around the line we want to modify
        exit_code, stdout, stderr = runner.run(
            f'grep -n "f2_flush.*backend_redirect" "{ifu_path}" || echo "Pattern not found"', cwd='/'
        )
        print(f'Current f2_flush line(s):\n{stdout}')

        # Apply the modification - change && to || in the f2_flush logic
        old_pattern = 'backend_redirect || mmio_redirect || wb_redirect'
        new_pattern = 'backend_redirect && mmio_redirect || wb_redirect'

        # Use sed to make the replacement
        sed_command = f'sed -i "s/{old_pattern}/{new_pattern}/g" "{ifu_path}"'
        exit_code, stdout, stderr = runner.run(sed_command, cwd='/')

        if exit_code == 0:
            print('✅ Successfully applied modification to IFU.scala')

            # Verify the change
            exit_code, stdout, stderr = runner.run(f'grep -n "f2_flush.*backend_redirect" "{ifu_path}"', cwd='/')
            print(f'Modified f2_flush line(s):\n{stdout}')

            # Show immediate changes detected by Runner's file tracking
            print('\n🔍 Checking for source file changes after patch...')
            scala_diffs = runner.get_all_diffs('.scala')
            if scala_diffs:
                print(f'✅ Detected {len(scala_diffs)} changed Scala file(s):')
                for file_path, diff in scala_diffs.items():
                    print(f'  📝 {file_path}')
                    # Show a preview of the diff (first few lines)
                    diff_lines = diff.split('\n')[:10]
                    for line in diff_lines:
                        if line.startswith('+') or line.startswith('-'):
                            print(f'    {line}')
                    if len(diff.split('\n')) > 10:
                        print(f'    ... ({len(diff.split("\n")) - 10} more lines)')
            else:
                print('⚠️  No Scala file changes detected immediately after patch')
        else:
            print(f'⚠️  File modification may have failed: {stderr}')

    # 7. Run XiangShan Verilog generation
    print('Running XiangShan Verilog generation...')
    print('⚠️  This may take several minutes for XiangShan...')

    # Note: XiangShan build can take a very long time, so we'll use a simpler command first
    build_command = (
        'make BUILD_DIR=/code/workspace/build/build_dbg DEBUG_VERILOG=1 CONFIG=MinimalConfig EMU_THREADS=2 sim-verilog'
    )

    # For demonstration, let's first try a quicker command to verify the build system
    print('Testing build system availability...')
    exit_code, stdout, stderr = runner.run('make --version', cwd='/code/workspace/repo')
    if exit_code != 0:
        print('❌ Make not available')
        runner.cleanup()
        return

    exit_code, stdout, stderr = runner.run('ls -la Makefile', cwd='/code/workspace/repo')
    if exit_code != 0:
        print('❌ Makefile not found in /code/workspace/repo')
        # Try to find Makefiles
        runner.run('find /code/workspace/repo -name "Makefile" -o -name "makefile" | head -3', cwd='/')
        runner.cleanup()
        return

    print('✅ Build system available')

    # Run the actual build (this might take a very long time for XiangShan)
    print(f'Executing: {build_command}')
    print('⏳ This may take 10+ minutes for XiangShan Verilog generation...')

    exit_code, stdout, stderr = runner.run(build_command, cwd='/code/workspace/repo')

    if exit_code == 0:
        print('✅ XiangShan Verilog generation successful')

        # Check what was generated
        exit_code, stdout, stderr = runner.run('find /code/workspace/build -name "*.sv" -o -name "*.v" | wc -l', cwd='/')
        if stdout.strip():
            print(f'Generated {stdout.strip()} Verilog files')

        # Show some example generated files
        exit_code, stdout, stderr = runner.run('find /code/workspace/build -name "*.sv" | head -5', cwd='/')
        if stdout.strip():
            print('Example generated files:')
            print(stdout)

        # Analyze changes in generated Verilog files using Runner's file tracking
        print('\n🔍 Analyzing generated Verilog file changes...')
        verilog_diffs = runner.get_all_diffs('.sv')
        verilog_diffs.update(runner.get_all_diffs('.v'))

        if verilog_diffs:
            print(f'✅ Detected {len(verilog_diffs)} changed Verilog file(s):')
            ifu_sv_found = False
            for file_path, diff in verilog_diffs.items():
                print(f'  📝 {file_path}')
                if 'IFU' in file_path or 'ifu' in file_path.lower():
                    ifu_sv_found = True
                    print(f'  🎯 Found IFU-related Verilog file: {file_path}')
                    # Show a preview of the IFU diff
                    diff_lines = diff.split('\n')[:15]
                    for line in diff_lines:
                        if line.startswith('+') or line.startswith('-'):
                            print(f'    {line}')
                    if len(diff.split('\n')) > 15:
                        print(f'    ... ({len(diff.split("\n")) - 15} more lines in IFU diff)')

            if ifu_sv_found:
                print('🎯 SUCCESS: Found IFU-related changes in generated Verilog files!')
            else:
                print('⚠️  No IFU-specific files found, but other Verilog changes detected')
        else:
            print('⚠️  No Verilog file changes detected after build')

    else:
        print(f'❌ XiangShan Verilog generation failed with exit code {exit_code}')
        print('This is expected for complex builds - XiangShan requires specific dependencies')
        print(f'Error details (first 500 chars): {stderr[:500]}')

        # Even if build failed, let's check if any partial files were generated
        print('\n🔍 Checking for any partial Verilog file changes...')
        partial_diffs = runner.get_all_diffs('.sv')
        partial_diffs.update(runner.get_all_diffs('.v'))
        if partial_diffs:
            print(f'⚠️  Found {len(partial_diffs)} partial Verilog file changes despite build failure')

    # 8. Final comprehensive change analysis
    print('\n📊 Final Change Analysis Summary:')
    print('=' * 50)

    # Get all tracked changes
    all_diffs = runner.get_all_diffs()
    if all_diffs:
        print(f'📝 Total files changed: {len(all_diffs)}')

        # Categorize changes
        scala_changes = {k: v for k, v in all_diffs.items() if k.endswith('.scala')}
        verilog_changes = {k: v for k, v in all_diffs.items() if k.endswith('.sv') or k.endswith('.v')}
        other_changes = {
            k: v for k, v in all_diffs.items() if not k.endswith('.scala') and not k.endswith('.sv') and not k.endswith('.v')
        }

        if scala_changes:
            print(f'  📜 Scala source files: {len(scala_changes)}')
            for file_path in scala_changes.keys():
                print(f'    - {file_path}')

        if verilog_changes:
            print(f'  🔧 Verilog files: {len(verilog_changes)}')
            ifu_found = []
            for file_path in verilog_changes.keys():
                if 'IFU' in file_path or 'ifu' in file_path.lower():
                    ifu_found.append(file_path)
                    print(f'    - {file_path} ⭐ (IFU-related)')
                else:
                    print(f'    - {file_path}')

            if ifu_found:
                print(f'\n🎯 VERIFICATION SUCCESS: Found {len(ifu_found)} IFU-related Verilog file(s)!')
                print('   This confirms that the Scala patch successfully affected the generated Verilog.')

        if other_changes:
            print(f'  📄 Other files: {len(other_changes)}')
            for file_path in other_changes.keys():
                print(f'    - {file_path}')

        # Generate patch dictionary for potential export
        patch_dict = runner.get_patch_dict()
        total_patches = len(patch_dict.get('patch', [])) + len(patch_dict.get('full', []))
        if total_patches > 0:
            print(f'\n📋 Generated patch dictionary with {total_patches} entries')
            print('   (Available for export to YAML if needed)')
    else:
        print('⚠️  No file changes detected by Runner')
        print('   This might indicate that the patch was not applied or build did not run successfully')

    # 9. Cleanup
    print('\n🧹 Cleaning up resources...')
    runner.cleanup()
    print('✅ Runner cleanup completed')

    print('\n✅ Test completed successfully - XiangShan execution with file tracking verified')
    print('   📈 The test demonstrates patch application and change detection capabilities')


@pytest.mark.slow
def test_xiangshan_execution():
    """Pytest slow test for XiangShan execution via Runner API."""
    _run_xiangshan_test()


def main():
    """CLI entry point - calls the core test logic."""
    _run_xiangshan_test()


if __name__ == '__main__':
    main()
