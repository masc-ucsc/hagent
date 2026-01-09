#!/usr/bin/env python3
"""
Verify MCP-generated Chisel diffs by calling v2chisel_batch directly.

This ensures IDENTICAL workflow to the hints-based approach, with proper:
- Baseline generation
- Diff application
- Compilation
- Golden design creation
- LEC verification
- CLEANUP and restoration

Usage:
    python verify_mcp_diff_v2.py \
        --bug 1 \
        --chisel-diff experiments/mcp_baseline/mcp_output/bug_01/chisel_diff.patch \
        --verilog-diff experiments/mcp_baseline/input/bug_01_Control.diff \
        --file Control.sv
"""

import sys
import argparse
from pathlib import Path

# Add hagent to path
sys.path.insert(0, str(Path.home() / 'hagent'))

from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch


def verify_mcp_diff(bug_number, chisel_diff_path, verilog_diff_path, bug_file):
    """
    Verify MCP-generated Chisel diff using v2chisel_batch directly.

    Args:
        bug_number: Bug ID (e.g., 1)
        chisel_diff_path: Path to Claude's generated Chisel diff
        verilog_diff_path: Path to target Verilog diff
        bug_file: Target file (e.g., 'Control.sv')

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

    # Create input data for v2chisel_batch
    # This is the EXACT format that v2chisel_batch expects
    input_data = {
        'bugs': [
            {
                'id': f'bug_{bug_number:02d}',
                'file': bug_file,
                'unified_diff': verilog_diff,
                # Provide the pre-generated Chisel diff from MCP agent
                '_mcp_chisel_diff': chisel_diff,  # Special key for bypass
            }
        ]
    }

    # Initialize v2chisel_batch processor
    print('\n🔧 Initializing v2chisel_batch processor...')
    processor = V2chisel_batch()

    # Run the processor with our input
    print('\n🚀 Running v2chisel_batch pipeline with MCP-generated diff...\n')
    result = processor.run(input_data)

    return result


def main():
    parser = argparse.ArgumentParser(description='Verify MCP-generated Chisel diffs using v2chisel_batch')
    parser.add_argument('--bug', type=int, required=True, help='Bug number')
    parser.add_argument('--chisel-diff', required=True, help='Path to Claude-generated Chisel diff')
    parser.add_argument('--verilog-diff', required=True, help='Path to target Verilog diff')
    parser.add_argument('--file', required=True, help='Target Verilog file (e.g., Control.sv)')

    args = parser.parse_args()

    result = verify_mcp_diff(
        bug_number=args.bug,
        chisel_diff_path=args.chisel_diff,
        verilog_diff_path=args.verilog_diff,
        bug_file=args.file,
    )

    # Print summary
    print(f'\n{"=" * 80}')
    print('📊 VERIFICATION SUMMARY')
    print(f'{"=" * 80}')
    print(f'Bug: {args.bug}')
    print(f'File: {args.file}')

    if result.get('success'):
        print('Result: ✅ SUCCESS')
        sys.exit(0)
    else:
        print('Result: ❌ FAILED')
        print(f'Error: {result.get("error", "Unknown error")}')
        sys.exit(1)


if __name__ == '__main__':
    main()
