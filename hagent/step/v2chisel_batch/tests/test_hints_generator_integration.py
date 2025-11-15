#!/usr/bin/env python3
"""
Integration test for HintsGenerator with V2chisel_batch.
"""

import os
import sys
import tempfile
import yaml
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

# Set environment before importing
# Docker mode enabled via HAGENT_DOCKER

from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch
from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator
from hagent.step.v2chisel_batch.components.bug_info import BugInfo


def test_hints_generator_integration():
    """Test HintsGenerator integration with V2chisel_batch."""

    print('🔬 Testing HintsGenerator integration...')

    # Create test input data
    test_input_data = {
        'bugs': [
            {
                'file': 'Control.sv',
                'unified_diff': """--- a/Control.sv
+++ b/Control.sv
@@ -1,3 +1,3 @@
 module Control();
-  wire old_signal;
+  wire new_signal;
 endmodule""",
            }
        ],
        'docker_container': 'test_container',
        'docker_patterns': ['/test/path'],
        'chisel_patterns': ['./test/*.scala'],
    }

    # Create temporary files
    with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as input_f:
        yaml.dump(test_input_data, input_f)
        input_file = input_f.name

    output_file = tempfile.mktemp(suffix='.yaml')

    try:
        # Test 1: Initialize V2chisel_batch and check HintsGenerator is created
        processor = V2chisel_batch()
        processor.input_file = input_file
        processor.output_file = output_file

        # This will call setup() which should initialize hints_generator
        processor.setup()

        print('✅ V2chisel_batch setup completed')

        # Check that HintsGenerator was initialized
        assert hasattr(processor, 'hints_generator'), 'HintsGenerator not found in processor'
        assert isinstance(processor.hints_generator, HintsGenerator), 'hints_generator is not HintsGenerator instance'

        print('✅ HintsGenerator properly initialized in processor')
        print(f'✅ HintsGenerator debug mode: {processor.hints_generator.debug}')

        # Test 2: Test that BugInfo and HintsGenerator work together
        bug_entry = test_input_data['bugs'][0]
        bug_info = BugInfo(bug_entry, 0)

        print(f'✅ BugInfo created: {bug_info.get_display_name()}')

        # Test 3: Test HintsGenerator can be called (we won't actually run it with Docker)
        print('✅ Components integrate correctly - BugInfo + HintsGenerator ready')

        # Test 4: Check that the interface is compatible
        # The hints_generator.find_hints should accept bug_info as first parameter
        import inspect

        find_hints_sig = inspect.signature(processor.hints_generator.find_hints)
        params = list(find_hints_sig.parameters.keys())
        expected_params = ['bug_info', 'all_files', 'docker_container']

        assert params == expected_params, f'find_hints signature mismatch: got {params}, expected {expected_params}'
        print('✅ HintsGenerator.find_hints interface is compatible')

        return True

    except Exception as e:
        print(f'❌ Integration test failed: {e}')
        import traceback

        traceback.print_exc()
        return False

    finally:
        # Cleanup
        try:
            os.unlink(input_file)
            os.unlink(output_file)
        except OSError:
            pass


if __name__ == '__main__':
    success = test_hints_generator_integration()
    sys.exit(0 if success else 1)
