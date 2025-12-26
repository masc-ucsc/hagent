#!/usr/bin/env python3
"""
Verify MCP-generated Chisel diffs using v2chisel_batch's LEC infrastructure.

Usage:
    python verify_mcp_diff.py \
        --bug 1 \
        --chisel-diff experiments/mcp_baseline/mcp_output/bug_01/chisel_diff.patch \
        --verilog-diff experiments/mcp_baseline/input/bug_01_Control.diff \
        --file Control.sv \
        --cpu singlecyclecpu_d
"""

import sys
import argparse
from pathlib import Path

# Add hagent to path
sys.path.insert(0, str(Path.home() / 'hagent'))

from hagent.inou.builder import Builder
from hagent.step.v2chisel_batch.components.golden_design_builder import GoldenDesignBuilder
from hagent.step.v2chisel_batch.components.docker_diff_applier import DockerDiffApplier
from hagent.step.v2chisel_batch.components.baseline_verilog_generator import BaselineVerilogGenerator
from hagent.core.equiv_check import Equiv_check


def verify_mcp_diff(bug_number, chisel_diff_path, verilog_diff_path, bug_file, cpu_profile='singlecyclecpu_d'):
    """
    Apply MCP-generated Chisel diff and verify with LEC.

    Args:
        bug_number: Bug ID (e.g., 1)
        chisel_diff_path: Path to Claude's generated Chisel diff
        verilog_diff_path: Path to target Verilog diff
        bug_file: Target file (e.g., 'Control.sv')
        cpu_profile: CPU profile to use (default: singlecyclecpu_d)

    Returns:
        dict with success status and details
    """
    print(f'\n{"=" * 80}')
    print(f'🧪 Verifying MCP-generated diff for Bug #{bug_number}: {bug_file}')
    print(f'{"=" * 80}\n')

    # Read diffs
    print(f'📖 Reading Chisel diff: {chisel_diff_path}')
    with open(chisel_diff_path) as f:
        chisel_diff = f.read()

    print(f'📖 Reading Verilog diff: {verilog_diff_path}')
    with open(verilog_diff_path) as f:
        verilog_diff = f.read()

    print('\n📝 Chisel diff preview:')
    print('-' * 40)
    print(chisel_diff[:500] + '...' if len(chisel_diff) > 500 else chisel_diff)
    print('-' * 40)

    # Initialize components (same as v2chisel_batch)
    print('\n🔧 Initializing Builder...')
    builder = Builder()
    if not builder.setup():
        error = builder.get_error()
        print(f'❌ Builder setup failed: {error}')
        return {'success': False, 'error': f'Builder setup failed: {error}', 'stage': 'builder_init'}

    print('✅ Builder initialized')

    # Initialize components
    applier = DockerDiffApplier(builder=builder, debug=True)
    golden_builder = GoldenDesignBuilder(builder=builder, debug=True)
    baseline_generator = BaselineVerilogGenerator(builder=builder, debug=True)
    equiv_check = Equiv_check()

    # Step 1: Generate baseline Verilog
    print(f'\n🏭 Generating baseline Verilog (profile: {cpu_profile})...')
    baseline_result = baseline_generator.generate_fresh_baseline(docker_container=None, verilog_files=[bug_file])

    if not baseline_result.get('success'):
        error = baseline_result.get('error', 'Unknown error')
        print(f'❌ Baseline generation failed: {error}')
        return {'success': False, 'error': error, 'stage': 'baseline'}

    print('✅ Baseline Verilog generated')

    # Step 2: Apply Chisel diff
    print('\n📝 Applying MCP-generated Chisel diff...')
    apply_success = applier.apply_diff_to_container(diff_content=chisel_diff, target_file_path=None, dry_run=False)

    if not apply_success:
        print('❌ Failed to apply Chisel diff')
        return {'success': False, 'error': 'Diff application failed', 'stage': 'apply'}

    print('✅ Chisel diff applied successfully')

    # Step 3: Compile
    print(f'\n🔨 Compiling Chisel (profile: {cpu_profile})...')
    compile_result = builder.run_api(api=cpu_profile)

    if compile_result.get('exit_code', 1) != 0:
        stderr = compile_result.get('stderr', '')
        print('❌ Compilation failed')
        print(f'Error: {stderr[:500]}')
        return {'success': False, 'error': 'Compilation failed', 'stderr': stderr, 'stage': 'compile'}

    print('✅ Compilation successful')

    # Step 4: Create golden design
    print('\n🎯 Creating golden design...')
    golden_result = golden_builder.create_golden_design(
        verilog_diff=verilog_diff, master_backup=baseline_result, docker_container=None
    )

    if not golden_result.get('success'):
        error = golden_result.get('error', 'Unknown error')
        print(f'❌ Golden design creation failed: {error}')
        return {'success': False, 'error': error, 'stage': 'golden'}

    print('✅ Golden design created')

    # Step 5: Run LEC
    print('\n🔍 Running LEC verification...')
    golden_dir = golden_result.get('golden_directory', '/code/workspace/repo/lec_golden')
    modified_dir = f'/code/workspace/build/build_{cpu_profile}'

    golden_file = f'{golden_dir}/{bug_file}'
    modified_file = f'{modified_dir}/{bug_file}'

    print(f'   Golden file: {golden_file}')
    print(f'   Modified file: {modified_file}')

    try:
        golden_verilog = builder.filesystem.read_text(golden_file)
        modified_verilog = builder.filesystem.read_text(modified_file)
    except Exception as e:
        print(f'❌ Failed to read Verilog files: {e}')
        return {'success': False, 'error': f'File read error: {e}', 'stage': 'lec_read'}

    module_name = bug_file.replace('.sv', '').replace('.v', '')
    print(f'   Module to compare: {module_name}')

    lec_result = equiv_check.check_equivalence(gold_code=golden_verilog, gate_code=modified_verilog, desired_top=module_name)

    if lec_result is True:
        print('\n✅ LEC PASSED - Designs are logically equivalent!')
        return {'success': True, 'lec_passed': True, 'bug': bug_number, 'file': bug_file, 'stage': 'complete'}
    else:
        print('\n❌ LEC FAILED - Designs are NOT logically equivalent')
        counterexample = ''
        if lec_result is False:
            counterexample = equiv_check.get_counterexample()
            print('\n📊 Counterexample:')
            print(counterexample[:1000])

        return {
            'success': False,
            'lec_passed': False,
            'error': 'LEC verification failed',
            'counterexample': counterexample,
            'bug': bug_number,
            'file': bug_file,
            'stage': 'lec',
        }


def main():
    parser = argparse.ArgumentParser(description='Verify MCP-generated Chisel diffs using v2chisel_batch infrastructure')
    parser.add_argument('--bug', type=int, required=True, help='Bug number')
    parser.add_argument('--chisel-diff', required=True, help='Path to Claude-generated Chisel diff')
    parser.add_argument('--verilog-diff', required=True, help='Path to target Verilog diff')
    parser.add_argument('--file', required=True, help='Target Verilog file (e.g., Control.sv)')
    parser.add_argument('--cpu', default='singlecyclecpu_d', help='CPU profile (default: singlecyclecpu_d)')

    args = parser.parse_args()

    result = verify_mcp_diff(
        bug_number=args.bug,
        chisel_diff_path=args.chisel_diff,
        verilog_diff_path=args.verilog_diff,
        bug_file=args.file,
        cpu_profile=args.cpu,
    )

    # Print summary
    print(f'\n{"=" * 80}')
    print('📊 VERIFICATION SUMMARY')
    print(f'{"=" * 80}')
    print(f'Bug: {result.get("bug", args.bug)}')
    print(f'File: {result.get("file", args.file)}')
    print(f'Stage: {result.get("stage", "unknown")}')

    if result['success']:
        print('Result: ✅ SUCCESS - LEC PASSED')
        sys.exit(0)
    else:
        print('Result: ❌ FAILED')
        print(f'Error: {result.get("error", "Unknown error")}')
        sys.exit(1)


if __name__ == '__main__':
    main()
