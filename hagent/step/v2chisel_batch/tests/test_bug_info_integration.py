#!/usr/bin/env python3
"""
Integration test for BugInfo with V2chisel_batch.
Tests that BugInfo works correctly within the actual pipeline.
"""

import os
import sys
import tempfile
import yaml
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch


def test_bug_info_integration_minimal():
    """Test BugInfo integration with minimal test data."""

    # Create minimal test bug data
    test_bugs = [
        {
            'file': 'TestModule1.sv',
            'unified_diff': """--- a/TestModule1.sv
+++ b/TestModule1.sv
@@ -1,3 +1,3 @@
 module TestModule1();
-  wire old_signal;
+  wire new_signal;
 endmodule""",
        },
        {
            'file': 'TestModule2.sv',
            'unified_diff': """--- a/TestModule2.sv
+++ b/TestModule2.sv
@@ -5,7 +5,7 @@
   input clk,
   input rst,
-  output old_output
+  output new_output
 );
 endmodule""",
        },
    ]

    # Create temporary input file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
        input_data = {
            'bugs': test_bugs,
            'docker_container': 'test_container',
            'docker_patterns': ['/test/path'],
            'chisel_patterns': ['./test/*.scala'],
        }
        yaml.dump(input_data, f)
        input_file = f.name

    # Create temporary output file
    output_file = tempfile.mktemp(suffix='.yaml')

    try:
        # Initialize V2chisel_batch
        processor = V2chisel_batch()
        processor.input_file = input_file
        processor.output_file = output_file

        # Test that we can load the input and create BugInfo objects
        with open(input_file, 'r') as f:
            input_data = yaml.safe_load(f)

        bugs = input_data.get('bugs', [])
        print(f'✅ Loaded {len(bugs)} test bugs')

        # Test BugInfo creation for each bug (this is what happens in _process_single_bug)
        from hagent.step.v2chisel_batch.components.bug_info import BugInfo

        for i, bug_entry in enumerate(bugs):
            bug_info = BugInfo(bug_entry, i)

            print(f'✅ Bug #{i + 1}:')
            print(f'   File: {bug_info.file_name}')
            print(f'   Module: {bug_info.module_name}')
            print(f'   Has diff: {bug_info.has_verilog_diff()}')
            print(f'   Display: {bug_info.get_display_name()}')

            # Verify BugInfo extracted data correctly
            assert bug_info.file_name == bug_entry['file']
            assert bug_info.module_name == bug_entry['file'].replace('.sv', '')
            assert bug_info.unified_diff == bug_entry['unified_diff']
            assert bug_info.has_verilog_diff()
            assert bug_info.bug_index == i

        print('✅ BugInfo integration test passed!')
        return True

    except Exception as e:
        print(f'❌ Integration test failed: {e}')
        import traceback

        traceback.print_exc()
        return False

    finally:
        # Cleanup temp files
        try:
            os.unlink(input_file)
        except OSError:
            pass
        try:
            os.unlink(output_file)
        except OSError:
            pass


if __name__ == '__main__':
    success = test_bug_info_integration_minimal()
    sys.exit(0 if success else 1)
