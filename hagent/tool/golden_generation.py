#!/usr/bin/env python3
"""
Golden Design Generation - CORRECTED strategy using existing original Verilog files
"""


def design_golden_generation_strategy():
    """Design the CORRECTED golden design generation strategy"""

    print('🎯 CORRECTED GOLDEN DESIGN GENERATION STRATEGY')
    print('=' * 65)

    print('\n📊 CORRECTED STRATEGY OVERVIEW:')
    print('   🎯 Goal: Create golden design = original Verilog + verilog_diff')
    print('   📁 Input: EXISTING original Verilog files + target verilog_diff')
    print('   🔧 Tool: Existing docker_diff_applier.py')
    print('   📦 Output: Golden design files for LEC comparison')

    print('\n✅ KEY INSIGHT: Original Verilog files ALREADY EXIST!')
    print('   📍 Path: {HAGENT_BUILD_DIR}/build_pipelined_d/*.sv (auto-translated by Builder)')
    print('   🗂️  Files: ALU.sv, Control.sv, PipelinedDualIssueCPU.sv, etc.')

    print('\n🔄 CORRECTED GOLDEN DESIGN GENERATION FLOW:')
    steps = [
        '📋 Receive verilog_diff (target changes)',
        '📁 Find EXISTING original Verilog in {HAGENT_BUILD_DIR}/build_pipelined_d/ (Builder auto-translates)',
        '💾 Backup original Verilog files (for safety)',
        '🏗️  Create golden design directory in container',
        '📋 Copy original Verilog files to golden design directory',
        '📝 Apply verilog_diff to golden design files using docker_diff_applier',
        '✅ Validate golden design files are created successfully',
        '🔍 Ready for LEC comparison with gate design',
    ]

    for i, step in enumerate(steps, 1):
        print(f'   {i}. {step}')

    return True


def show_corrected_implementation():
    """Show the corrected implementation strategy"""

    print('\n🏗️ CORRECTED IMPLEMENTATION STRATEGY')
    print('=' * 50)

    print('\n1️⃣ ACTUAL FILE STRUCTURE IN DOCKER:')
    print('   {Builder auto-translates paths}')
    print('   ├── {HAGENT_BUILD_DIR}/build_pipelined_d/  # ORIGINAL Verilog files (EXISTING)')
    print('   │   ├── ALU.sv')
    print('   │   ├── Control.sv')
    print('   │   ├── PipelinedDualIssueCPU.sv')
    print('   │   ├── DualIssueHazardUnit.sv')
    print('   │   └── [other .sv files]')
    print('   ├── {HAGENT_REPO_DIR}/src/main/scala/      # Chisel source code')
    print('   │   ├── Main.scala')
    print('   │   ├── components/')
    print('   │   └── pipelined/')
    print('   └── {HAGENT_REPO_DIR}/lec_golden/          # Golden design (created)')
    print('       ├── ALU.sv                             # original + verilog_diff')
    print('       ├── Control.sv                         # original + verilog_diff')
    print('       └── PipelinedDualIssueCPU.sv           # original + verilog_diff')

    print('\n2️⃣ CORRECTED GOLDEN GENERATION ALGORITHM:')
    algorithm = [
        {
            'step': 'Find existing original Verilog',
            'details': 'Use builder.translate_path() to locate files in {HAGENT_BUILD_DIR}/build_pipelined_d/*.sv',
            'example': 'Found: ALU.sv, Control.sv, PipelinedDualIssueCPU.sv',
        },
        {
            'step': 'Backup original files',
            'details': 'Copy originals to backup location for safety',
            'example': 'Use builder.filesystem.copy() with auto-translated paths',
        },
        {
            'step': 'Create golden directory',
            'details': 'Use builder.filesystem.mkdir() with auto-translated paths',
            'example': 'builder.filesystem.mkdir({HAGENT_REPO_DIR}/lec_golden/)',
        },
        {
            'step': 'Copy originals to golden',
            'details': 'Copy original Verilog files to golden design directory',
            'example': 'Use builder.filesystem.copy() with auto-translated paths',
        },
        {
            'step': 'Apply verilog_diff',
            'details': 'Use docker_diff_applier to apply verilog_diff to golden files',
            'example': 'docker_diff_applier.apply_diff(verilog_diff, builder.translate_path_to_container(golden_dir))',
        },
        {
            'step': 'Validate golden design',
            'details': 'Ensure golden files contain expected changes',
            'example': 'Check that lec_golden/Control.sv contains target modifications',
        },
    ]

    for i, alg in enumerate(algorithm, 1):
        print(f'   {i}. 🔧 {alg["step"]}')
        print(f'      📝 {alg["details"]}')
        print(f'      💡 Example: {alg["example"]}')
        print()

    return True


def show_corrected_code_implementation():
    """Show the corrected code implementation"""

    print('💻 CORRECTED CODE IMPLEMENTATION')
    print('=' * 40)

    print('\n1️⃣ CONFIGURATION:')
    print('```python')
    print('# Use Builder for automatic path translation')
    print("original_verilog_path = builder.translate_path(f'{PathManager().build_dir}/build_pipelined_d')")
    print("golden_design_path = builder.translate_path(f'{PathManager().repo_dir}/lec_golden')")
    print('```')

    print('\n2️⃣ CORRECTED _create_golden_design() method:')
    print('```python')
    print('def _create_golden_design(self, builder: Builder, verilog_diff: str) -> dict:')
    print('    """Create golden design using EXISTING original Verilog files"""')
    print('    try:')
    print('        # Use PathManager singleton for unified path management')
    print('        path_manager = PathManager()')
    print("        original_verilog_path = f'{path_manager.build_dir}/build_pipelined_d'")
    print("        golden_dir = f'{path_manager.repo_dir}/lec_golden'")
    print('        ')
    print('        # Translate paths for the execution environment')
    print('        container_original_path = builder.translate_path_to_container(original_verilog_path)')
    print('        container_golden_dir = builder.translate_path_to_container(golden_dir)')
    print('        ')
    print('        # Find existing original Verilog files using Builder')
    print('        rc, out, err = builder.run_cmd(f\'find {container_original_path} -name "*.sv" -type f\')')
    print('        ')
    print('        if find_result.returncode != 0 or not find_result.stdout.strip():')
    print("            return {'success': False, 'error': 'No original Verilog files found'}")
    print('        ')
    print("        original_files = [f.strip() for f in find_result.stdout.strip().split('\\n')]")
    print("        print(f'📁 [GOLDEN] Found {len(original_files)} original Verilog files')")
    print('        ')
    print('        # Create golden design directory')
    print("        mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', golden_dir]")
    print('        subprocess.run(mkdir_cmd, check=True)')
    print('        ')
    print('        # Copy original files to golden directory')
    print('        copied_files = []')
    print('        for original_file in original_files:')
    print("            filename = original_file.split('/')[-1]")
    print("            golden_file = f'{golden_dir}/{filename}'")
    print('            ')
    print("            copy_cmd = ['docker', 'exec', docker_container, 'cp', original_file, golden_file]")
    print('            copy_result = subprocess.run(copy_cmd, capture_output=True)')
    print('            ')
    print('            if copy_result.returncode == 0:')
    print('                copied_files.append(golden_file)')
    print("                print(f'     ✅ Copied to golden: {filename}')")
    print('        ')
    print('        # Apply verilog_diff using docker_diff_applier')
    print('        from hagent.tool.docker_diff_applier import DockerDiffApplier')
    print('        applier = DockerDiffApplier(docker_container)')
    print('        ')
    print('        diff_result = applier.apply_unified_diff(verilog_diff, base_path=golden_dir)')
    print('        ')
    print("        if diff_result.get('success', False):")
    print('            return {')
    print("                'success': True,")
    print("                'golden_files': copied_files,")
    print("                'golden_directory': golden_dir,")
    print("                'original_verilog_path': original_verilog_path")
    print('            }')
    print('        else:')
    print("            return {'success': False, 'error': diff_result.get('error', 'Unknown error')}")
    print('            ')
    print('    except Exception as e:')
    print("        return {'success': False, 'error': f'Golden design creation failed: {str(e)}'}")
    print('```')

    return True


def show_comparison_with_old_approach():
    """Show comparison between old incorrect and new correct approach"""

    print('\n🔄 COMPARISON: OLD vs NEW APPROACH')
    print('=' * 45)

    print('\n❌ OLD INCORRECT APPROACH:')
    print("   1. Generate 'baseline' Verilog from original Chisel")
    print('   2. Backup this generated baseline')
    print("   3. Generate 'gate' Verilog from modified Chisel")
    print('   4. Create golden design = baseline + verilog_diff')
    print('   5. Run LEC: golden vs gate')
    print('   ⚠️  Problem: Unnecessary generation, wrong assumption!')

    print('\n✅ NEW CORRECT APPROACH:')
    print('   1. Find EXISTING original Verilog files')
    print('   2. Copy originals to golden design directory')
    print('   3. Apply verilog_diff to golden design files')
    print('   4. Generate gate Verilog from modified Chisel')
    print('   5. Run LEC: golden vs gate')
    print('   ✨ Benefits: Uses actual original files, simpler, faster!')

    print('\n🎯 KEY DIFFERENCES:')
    differences = [
        'Original source: Generated baseline → EXISTING files',
        'Baseline step: Generate from Chisel → Copy from build directory',
        'Performance: Slower (extra generation) → Faster (direct copy)',
        'Accuracy: Potential inconsistency → Uses actual original files',
    ]

    for diff in differences:
        old, new = diff.split(' → ')
        print(f'   • {old} → {new}')

    return True


if __name__ == '__main__':
    design_golden_generation_strategy()
    show_corrected_implementation()
    show_corrected_code_implementation()
    show_comparison_with_old_approach()
