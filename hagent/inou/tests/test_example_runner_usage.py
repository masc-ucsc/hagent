#!/usr/bin/env python3
"""
Example showing how existing cli_executor* files can be simplified using Runner.

This demonstrates the before/after comparison of using Runner vs direct usage
of Executor, ContainerManager, PathManager, and FileTracker.
"""

import os
from hagent.inou.runner import Runner


def example_simplechisel_with_runner():
    """
    Simplified version of cli_executor_simplechisel.py using Runner.

    Compare this with the original 99-line file that manually manages:
    - PathManager initialization
    - ContainerManager setup
    - ExecutorFactory.create_executor calls
    - Manual cleanup of container_manager
    """

    # Set execution mode
    # Docker mode enabled via HAGENT_DOCKER

    # Create Runner - automatically handles all the setup
    with Runner(docker_image='mascucsc/hagent-simplechisel:2025.11') as runner:
        # Setup execution environment
        if not runner.setup():
            print(f'Setup failed: {runner.get_error()}')
            return

        print('✅ Container setup successful')

        # Check if SimpleChisel project exists
        print('Checking for SimpleChisel project...')
        exit_code, stdout, stderr = runner.run_cmd('ls -la /code/workspace/repo/', cwd='/')

        if exit_code != 0:
            print('⚠️  SimpleChisel project not found in expected locations')
            return

        print('✅ Found SimpleChisel project at: /code/workspace/repo')

        # Execute SBT compile command
        print('Running SBT compile...')
        exit_code, stdout, stderr = runner.run_cmd('sbt compile', cwd='/code/workspace/repo')

        if exit_code != 0:
            print(f'❌ sbt compile failed: {stderr}')
            return

        print('✅ SBT compile successful')

        # Execute SBT runMain command
        print('Running SBT runMain...')
        exit_code, stdout, stderr = runner.run_cmd(
            'sbt "runMain dinocpu.pipelined.PipelinedDualIssueDebug"', cwd='/code/workspace/repo'
        )

        if exit_code != 0:
            print(f'❌ sbt runMain failed: {stderr}')
            return

        print('✅ SBT runMain successful')
        print('✅ Test completed successfully - SimpleChisel execution verified')

    # Cleanup happens automatically via context manager


def example_xiangshan_with_runner_and_tracking():
    """
    Simplified version of cli_executor_xiangshan.py using Runner with file tracking.

    This shows how Runner makes file tracking much simpler compared to the original
    315-line file that manually manages FileTracker initialization and cleanup.
    """

    # Set execution mode
    # Docker mode enabled via HAGENT_DOCKER

    with Runner(docker_image='mascucsc/hagent-xiangshan:2025.09') as runner:
        if not runner.setup():
            print(f'Setup failed: {runner.get_error()}')
            return

        print('✅ Container setup successful')

        # Check XiangShan project structure
        print('Checking XiangShan project structure...')
        exit_code, stdout, stderr = runner.run_cmd('ls -la /code/workspace/repo/', cwd='/')

        if exit_code != 0:
            print('❌ XiangShan project not found')
            return

        print('✅ Found XiangShan project at: /code/workspace/repo')

        # Setup file tracking (lazy initialization)
        print('🔍 Setting up file tracking...')

        # Track source files that we'll modify
        runner.track_file('src/main/scala/xiangshan/frontend/IFU.scala')
        runner.track_dir('src/main/scala/xiangshan/frontend', '.scala')

        # Track generated Verilog files
        runner.track_dir('build', '.sv')
        runner.track_dir('build', '.v')

        print('✅ File tracking configured')

        # Apply modification to IFU.scala
        ifu_path = '/code/workspace/repo/src/main/scala/xiangshan/frontend/IFU.scala'

        print('Applying test modification to IFU.scala...')
        old_pattern = 'backend_redirect || mmio_redirect || wb_redirect'
        new_pattern = 'backend_redirect && mmio_redirect || wb_redirect'

        exit_code, stdout, stderr = runner.run_cmd(f'sed -i "s/{old_pattern}/{new_pattern}/g" "{ifu_path}"', cwd='/')

        if exit_code == 0:
            print('✅ Successfully applied modification to IFU.scala')

            # Show source file changes immediately
            print('🔍 Checking for source file changes...')
            scala_diffs = runner.get_all_diffs('.scala')

            if scala_diffs:
                print(f'✅ Detected {len(scala_diffs)} changed Scala file(s):')
                for file_path in scala_diffs.keys():
                    print(f'  📝 {file_path}')
            else:
                print('⚠️  No Scala file changes detected')

        # Run XiangShan Verilog generation
        print('Running XiangShan Verilog generation...')
        build_command = (
            'make BUILD_DIR=/code/workspace/build/build_dbg DEBUG_VERILOG=1 CONFIG=MinimalConfig EMU_THREADS=2 sim-verilog'
        )

        exit_code, stdout, stderr = runner.run_cmd(build_command, cwd='/code/workspace/repo')

        if exit_code == 0:
            print('✅ XiangShan Verilog generation successful')

            # Analyze Verilog changes using Runner's simple API
            print('🔍 Analyzing generated Verilog file changes...')
            verilog_diffs = runner.get_all_diffs('.sv')
            verilog_diffs.update(runner.get_all_diffs('.v'))

            if verilog_diffs:
                print(f'✅ Detected {len(verilog_diffs)} changed Verilog file(s)')

                # Look for IFU-related changes
                ifu_files = [f for f in verilog_diffs.keys() if 'IFU' in f or 'ifu' in f.lower()]

                if ifu_files:
                    print(f'🎯 SUCCESS: Found {len(ifu_files)} IFU-related Verilog file(s)!')
                    print('   This confirms that the Scala patch affected the generated Verilog.')
            else:
                print('⚠️  No Verilog file changes detected')
        else:
            print(f'❌ Build failed: {stderr[:200]}...')

        # Generate comprehensive change summary
        print('\n📊 Final Change Analysis:')
        all_diffs = runner.get_all_diffs()

        if all_diffs:
            print(f'📝 Total files changed: {len(all_diffs)}')

            scala_changes = {k: v for k, v in all_diffs.items() if k.endswith('.scala')}
            verilog_changes = {k: v for k, v in all_diffs.items() if k.endswith('.sv') or k.endswith('.v')}

            if scala_changes:
                print(f'  📜 Scala source files: {len(scala_changes)}')
            if verilog_changes:
                print(f'  🔧 Verilog files: {len(verilog_changes)}')

            # Generate patch dictionary for export
            patch_dict = runner.get_patch_dict()
            total_patches = len(patch_dict.get('patch', [])) + len(patch_dict.get('full', []))

            if total_patches > 0:
                print(f'📋 Generated patch dictionary with {total_patches} entries')
        else:
            print('⚠️  No file changes detected')

        print('✅ Test completed - XiangShan execution with file tracking verified')

    # All cleanup handled automatically by context manager


def example_trivial_step_with_runner():
    """
    Simplified version of trivial.py using Runner.

    Shows how Step classes can use Runner instead of manually managing
    ContainerManager and ExecutorFactory.
    """

    # This could be in the Step.setup() method
    if os.getenv('HAGENT_DOCKER'):
        runner = Runner(docker_image='mascucsc/hagent-simplechisel:2025.11')
    else:
        runner = Runner()  # Local mode

    if not runner.setup():
        print(f'Setup failed: {runner.get_error()}')
        return

    # Run commands
    exit_code, stdout, stderr = runner.run_cmd('uname -a')
    print(f'uname: {stdout.strip()}')

    exit_code, stdout, stderr = runner.run_cmd('pwd')
    print(f'pwd: {stdout.strip()}')

    exit_code, stdout, stderr = runner.run_cmd('which yosys')
    print(f'yosys path: {stdout.strip() if exit_code == 0 else "not found"}')

    runner.cleanup()


if __name__ == '__main__':
    print('=== Example 1: SimpleChisel with Runner ===')
    example_simplechisel_with_runner()

    print('\n=== Example 2: XiangShan with Runner and File Tracking ===')
    example_xiangshan_with_runner_and_tracking()

    print('\n=== Example 3: Trivial Step with Runner ===')
    example_trivial_step_with_runner()
