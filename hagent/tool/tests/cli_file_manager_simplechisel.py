#!/usr/bin/env python3
"""
Simple test example for File_manager tracking functionality.
Demonstrates track_file, track_dir, and patch generation.
"""

import sys
import pytest

# Add the hagent package to the path
sys.path.insert(0, '/Users/renau/projs/hagent')

from hagent.tool.file_manager import File_manager


def test_main():
    """Simple example of File_manager usage with tracking."""

    # 1. Initialize and setup
    fm = File_manager('mascucsc/hagent-simplechisel:2025.07')

    assert fm.setup(), f'Setup failed: {fm.get_error()}'

    # 2. Track existing files before making changes
    # Extensions are now specified per directory via track_dir()

    # 3. Check if target files exist before tracking
    fm.track_dir( '/code/simplechisel/src/main/scala', ext=".scala")
    fm.track_dir( '/code/simplechisel/build_singlecyclecpu_nd', ext=".sv")
    fm.track_dir( '/code/simplechisel/build_singlecyclecpu_d', ext=".sv")
    # fm.track_dir( '/code/simplechisel/build_pipelined_nd', ext=".sv")
    fm.track_dir( '/code/simplechisel/build_pipelined_d', ext=".sv")
    fm.track_dir( '/code/simplechisel/build_gcd', ext=".sv")

    # Just compile check, no Verilog generate
    exit_code, stdout, stderr = fm.run('sbt compile', container_path='/code/simplechisel')
    assert exit_code == 0, f'sbt compile failed: {fm.get_error()} code:{exit_code}\nstderr: {stderr}'

    # Commands:
    # sbt "runMain gcd.GCD"
    # sbt "runMain dinocpu.SingleCycleCPUNoDebug"
    # sbt "runMain dinocpu.SingleCycleCPUDebug"
    # sbt "runMain dinocpu.pipelined.PipelinedDualIssueDebug"
    exit_code, stdout, stderr = fm.run('sbt "runMain dinocpu.pipelined.PipelinedDualIssueDebug"', container_path='/code/simplechisel')
    assert exit_code == 0, f'sbt runMain failed: {fm.get_error()} code:{exit_code}\nstderr: {stderr}'

    # 5. Generate and save patches (no edit, no changes expected)
    patches = fm.get_patch_dict()
    
    # Since no files were modified, patches should be empty
    assert not patches.get('patch', []), f'Expected no patches but got: {patches.get("patch", [])}'
    assert not patches.get('full', []), f'Expected no full files but got: {patches.get("full", [])}'
    
    print('Test completed successfully - no changes detected as expected')

if __name__ == '__main__':
    test_main()
