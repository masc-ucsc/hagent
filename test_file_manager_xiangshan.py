#!/usr/bin/env python3
"""
Test script for File_manager with xiangshan image.
Tests the new track_file and track_dir functionality.
"""

import sys
import os
import tempfile

# Add the hagent package to the path
sys.path.insert(0, '/Users/renau/projs/hagent')

from hagent.tool.file_manager import File_manager


def test_xiangshan_tracking():
    """Test tracking and patching files in the xiangshan container."""
    
    print("=== File_manager XiangShang Test ===")
    
    # Initialize File_manager with xiangshan image
    fm = File_manager("masc-ucsc/hagent-xiangshan:latest")
    
    # Check Docker connection
    docker_info = fm.get_docker_info()
    print(f"Docker status: {docker_info.get('status', 'Unknown')}")
    if docker_info['status'] != 'CONNECTED':
        print(f"Docker error: {docker_info.get('message', 'Unknown error')}")
        return False
    
    # Setup the container
    print("Setting up container...")
    if not fm.setup():
        print(f"Setup failed: {fm.get_error()}")
        return False
    
    # Check if XiangShang directory exists
    print("Checking XiangShang directory...")
    exit_code, stdout, stderr = fm.run("ls -la /code/XiangShang", container_path=".")
    if exit_code != 0:
        print(f"XiangShang directory not found: {stderr}")
        return False
    
    print("XiangShang directory contents:")
    print(stdout)
    
    # Track specific Scala files in the frontend directory
    print("\nTracking frontend Scala files...")
    fm.add_tracking_extension(".scala")
    
    # Create a symbolic link to XiangShang in the working directory for easier access
    print("Creating symbolic link to XiangShang...")
    exit_code, stdout, stderr = fm.run("ln -sf /code/XiangShang ./xiangshan", container_path=".")
    
    # Track the IFU.scala file specifically
    target_file = "xiangshan/src/main/scala/xiangshan/frontend/IFU.scala"
    
    # First check if the file exists by trying to read it
    exit_code, stdout, stderr = fm.run(f"test -f {target_file} && echo 'File exists' || echo 'File not found'", container_path=".")
    print(f"File check result: {stdout.strip()}")
    
    if "File not found" in stdout:
        print("IFU.scala not found, listing frontend directory...")
        exit_code, stdout, stderr = fm.run("find xiangshan -name 'IFU.scala' -type f", container_path=".")
        print(f"IFU.scala search result: {stdout}")
        if stdout.strip():
            target_file = stdout.strip().split('\n')[0]
            print(f"Found IFU.scala at: {target_file}")
        else:
            print("Could not locate IFU.scala file")
            return False
    
    # Track the file
    print(f"\nTracking file: {target_file}")
    if not fm.track_file(target_file):
        print(f"Failed to track file: {fm.get_error()}")
        return False
    
    # Show original content snippet
    print("\nOriginal IFU.scala content around line 257:")
    exit_code, stdout, stderr = fm.run(f"sed -n '250,260p' {target_file}")
    print(stdout)
    
    # Apply the patch - change line 257
    # Original: f2_flush         := backend_redirect || mmio_redirect || wb_redirect
    # New:      f2_flush         := backend_redirect && mmio_redirect || wb_redirect
    
    print("\nApplying patch...")
    patch_command = f"sed -i 's/f2_flush.*:= backend_redirect || mmio_redirect || wb_redirect/f2_flush         := backend_redirect \\&\\& mmio_redirect || wb_redirect/' {target_file}"
    exit_code, stdout, stderr = fm.run(patch_command)
    
    if exit_code != 0:
        print(f"Patch failed: {stderr}")
        return False
    
    # Show modified content
    print("\nModified IFU.scala content around line 257:")
    exit_code, stdout, stderr = fm.run(f"sed -n '250,260p' {target_file}")
    print(stdout)
    
    # Set up tracking for Verilog files
    print("\nSetting up tracking for Verilog files...")
    fm.add_tracking_extension(".v")
    fm.add_tracking_extension(".sv")
    
    # Create a symbolic link to XiangShang in the working directory for easier access
    print("Creating symbolic link to XiangShang...")
    exit_code, stdout, stderr = fm.run("ln -sf /code/XiangShang ./xiangshan", container_path=".")
    
    # Check if build/rtl directory exists and track it
    exit_code, stdout, stderr = fm.run("ls -la xiangshan/build/rtl/", container_path=".")
    if exit_code == 0:
        print("build/rtl directory exists, tracking existing files...")
        if not fm.track_dir("xiangshan/build/rtl", ext=".v"):
            print(f"Warning: Failed to track build/rtl Verilog files: {fm.get_error()}")
        if not fm.track_dir("xiangshan/build/rtl", ext=".sv"):
            print(f"Warning: Failed to track build/rtl SystemVerilog files: {fm.get_error()}")
    else:
        print("build/rtl directory doesn't exist yet, will be created by make")
    
    # Run the make command
    print("\nRunning make CONFIG=MinimalConfig EMU_THREADS=2 sim-verilog...")
    print("This may take several minutes...")
    
    exit_code, stdout, stderr = fm.run("cd xiangshan && make CONFIG=MinimalConfig EMU_THREADS=2 sim-verilog", container_path=".")
    
    print(f"Make command exit code: {exit_code}")
    if stdout:
        print("Make stdout (last 1000 chars):")
        print(stdout[-1000:] if len(stdout) > 1000 else stdout)
    if stderr:
        print("Make stderr (last 1000 chars):")
        print(stderr[-1000:] if len(stderr) > 1000 else stderr)
    
    # Check if build/rtl directory was created/modified
    print("\nChecking build/rtl directory after make...")
    exit_code, stdout, stderr = fm.run("find xiangshan/build/rtl -name '*.v' -o -name '*.sv' | head -10", container_path=".")
    print(f"Generated Verilog files (first 10):")
    print(stdout)
    
    # Generate patch dictionary
    print("\nGenerating patch dictionary...")
    patches = fm.get_patch_dict()
    
    if not patches:
        print("No patches generated!")
        return False
    
    print(f"Patches found: {len(patches.get('patch', []))} diffs, {len(patches.get('full', []))} full files")
    
    # Display the diff
    for patch in patches.get('patch', []):
        print(f"\n=== DIFF for {patch['filename']} ===")
        print(patch['diff'])
    
    for full_file in patches.get('full', []):
        print(f"\n=== FULL FILE: {full_file['filename']} ===")
        if len(full_file['contents']) > 1000:
            print(f"[Large file - {len(full_file['contents'])} characters]")
            print(full_file['contents'][:500] + "\n... [truncated] ...")
        else:
            print(full_file['contents'])
    
    # Save patches to YAML
    print("\nSaving patches to YAML...")
    if fm.save_patches("xiangshan_test_patches.yaml", "ifu_patch_test"):
        print("Patches saved to xiangshan_test_patches.yaml")
    else:
        print(f"Failed to save patches: {fm.get_error()}")
    
    print("\n=== Test completed successfully! ===")
    return True


if __name__ == "__main__":
    try:
        success = test_xiangshan_tracking()
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print("\nTest interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"Test failed with exception: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)