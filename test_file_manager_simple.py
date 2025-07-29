#!/usr/bin/env python3
"""
Simple test example for File_manager tracking functionality.
Demonstrates track_file, track_dir, and patch generation.
"""

import sys

# Add the hagent package to the path
sys.path.insert(0, '/Users/renau/projs/hagent')

from hagent.tool.file_manager import File_manager


def main():
    """Simple example of File_manager usage with tracking."""

    # 1. Initialize and setup
    fm = File_manager('mascucsc/hagent-xiangshan:2025.07')

    if not fm.setup():
        print(f'Setup failed: {fm.get_error()}')
        exit(2)

    # 2. Track existing files before making changes
    fm.add_tracking_extension('.scala')
    fm.add_tracking_extension('.v')
    fm.add_tracking_extension('.sv')

    # 3. Check if target files exist before tracking
    ifu_path = '/code/XiangShan/src/main/scala/xiangshan/frontend/IFU.scala'
    rtl_path = '/code/XiangShan/build/rtl'

    exit_code, stdout, stderr = fm.run(f'test -f "{ifu_path}"')
    if exit_code != 0:
        print(f'IFU.scala file not found: {fm.get_error()} code:{exit_code}')
        exit_code, stdout, stderr = fm.run('find /code/XiangShan -name IFU.scala')
        exit(4)

    exit_code, stdout, stderr = fm.run(f'test -d "{rtl_path}"')
    if exit_code != 0:
        print(f'RTL directory not found: {fm.get_error()} code:{exit_code}')
        exit(5)

    fm.track_file(ifu_path)
    fm.track_dir(rtl_path, ext='.sv')

    # 4. Apply the patch to IFU.scala using the proper API
    old_line = '  f2_flush         := backend_redirect || mmio_redirect || wb_redirect'
    new_line = '  f2_flush         := backend_redirect && mmio_redirect || wb_redirect'

    if not fm.apply_line_patch(ifu_path, 257, old_line, new_line):
        print(f'apply_line_patch failed: {fm.get_error()}')
        exit(6)

    #fm.run(f"grep f2_flush {ifu_path}")
    fm.run("id");
    fm.run("pwd", container_path="/code/XiangShan");

    l1 = "assign io_out_bits_ctrl_robIdx_value = io_in_bits_ctrlPipe_0_robIdx_value;"
    l2 = "assign io_out_bits_ctrl_robIdx_value = io_in_bits_ctrlPipe_0_robIdx_value - 1;"
    if not fm.apply_line_patch("/code/XiangShan/build/rtl/Alu.sv", 137, l1, l2):
        print(f'apply_line_patch2 failed: {fm.get_error()}')
        exit(6)

    # 5. Generate and save patches
    patches = fm.get_patch_dict()
    if not patches:
        print(f'get_patch_dict failed: {fm.get_error()}')
        exit(8)

    fm.save_patches('xiangshan_patches.yaml', 'example_run')

    # Display results
    print(f'Found {len(patches.get("patch", []))} diffs and {len(patches.get("full", []))} new files')

    for patch in patches.get('patch', []):
        print(f'\nDIFF: {patch["filename"]}')
        print(patch['diff'][:500] + '...' if len(patch['diff']) > 500 else patch['diff'])

    for full_file in patches.get('full', []):
        print(f'\nNEW FILE: {full_file["filename"]}')
        content = full_file['contents']
        if isinstance(content, str) and len(content) > 500:
            print(content[:500] + '...')
        else:
            print(content)


if __name__ == '__main__':
    main()
