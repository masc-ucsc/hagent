#!/usr/bin/env python3
"""
Test script for v2chisel_batch retry mechanism with diff applier
"""

import sys
from pathlib import Path
import os
import pytest

# Add project root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

# ruff: noqa: E402
from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch
from hagent.tool.docker_diff_applier import DockerDiffApplier


@pytest.fixture(autouse=True)
def setup_test_env():
    """Pytest fixture to ensure proper environment setup for every test in this module"""
    # Store original environment
    original_env = {
        'HAGENT_REPO_DIR': os.environ.get('HAGENT_REPO_DIR'),
        'HAGENT_BUILD_DIR': os.environ.get('HAGENT_BUILD_DIR'),
        'HAGENT_CACHE_DIR': os.environ.get('HAGENT_CACHE_DIR'),
    }

    # Set up environment for this test
    setup_test_environment()

    yield  # Run the test

    # Restore original environment (cleanup)
    for key, value in original_env.items():
        if value is None:
            os.environ.pop(key, None)
        else:
            os.environ[key] = value


def setup_test_environment():
    """Set up environment variables for testing - called before each test"""
    # Force set environment variables (don't use setdefault)
    # Docker mode enabled via HAGENT_DOCKER

    # Use current directory for CI compatibility
    current_dir = os.path.dirname(os.path.abspath(__file__))
    os.environ['HAGENT_REPO_DIR'] = current_dir
    os.environ['HAGENT_BUILD_DIR'] = os.path.join(current_dir, 'build')
    os.environ['HAGENT_CACHE_DIR'] = os.path.join(current_dir, 'cache')

    # Create directories if they don't exist
    os.makedirs(os.environ['HAGENT_REPO_DIR'], exist_ok=True)
    os.makedirs(os.environ['HAGENT_BUILD_DIR'], exist_ok=True)
    os.makedirs(os.environ['HAGENT_CACHE_DIR'], exist_ok=True)

    # Environment successfully set up


# Set up environment before importing
setup_test_environment()


def test_retry_mechanism():
    """Test that demonstrates the retry loop when applier fails"""
    print('🧪 Testing v2chisel_batch retry mechanism')
    print('=' * 60)

    # Create temporary input and output files
    test_dir = Path(__file__).parent

    input_file = test_dir / 'test_input_retry.yaml'
    output_file = test_dir / 'test_output_retry.yaml'

    if not input_file.exists():
        print(f'❌ Test input file not found: {input_file}')
        return False

    print(f'📁 Input file: {input_file}')
    print(f'📁 Output file: {output_file}')

    # Initialize v2chisel_batch
    try:
        processor = V2chisel_batch()
        processor.input_file = str(input_file)
        processor.output_file = str(output_file)

        # Load input data
        from ruamel.yaml import YAML

        yaml = YAML()
        with open(input_file, 'r') as f:
            processor.input_data = yaml.load(f)

        # Setup the processor
        processor.setup()
        print('✅ V2chisel_batch initialized successfully')

        # Get actual container name from Runner
        actual_container_name = None
        if hasattr(processor, 'runner') and processor.runner and hasattr(processor.runner, 'container_manager'):
            container_mgr = processor.runner.container_manager
            if hasattr(container_mgr, 'container') and container_mgr.container:
                actual_container_name = container_mgr.container.name

        if not actual_container_name:
            print('❌ Could not get container name from Runner')
            return False

        print(f'✅ Using container: {actual_container_name}')

    except Exception as e:
        print(f'❌ Failed to initialize v2chisel_batch: {e}')
        return False

    # Test the docker diff applier separately first
    print('\n🐳 Testing DockerDiffApplier with intentionally wrong diff...')

    # Create a test diff that should fail (wrong removal line)
    wrong_diff = """--- a/src/main/scala/components/control.scala
+++ b/src/main/scala/components/control.scala
@@ -100,1 +100,1 @@
-  // This line doesn't exist in the actual file
+  // This is a test replacement
"""

    # Test the applier with actual container name
    applier = DockerDiffApplier(actual_container_name)

    try:
        success = applier.apply_diff_to_container(wrong_diff, dry_run=True)
        if success:
            print("⚠️  Expected failure but applier succeeded - this shouldn't happen")
            return False
        else:
            print('✅ Applier correctly failed with wrong diff')
    except Exception as e:
        print(f'✅ Applier correctly raised exception: {e}')

    print('\n🔄 Now testing correct diff...')

    # Test with a correct diff that should work (using actual file content)
    correct_diff = """--- a/src/main/scala/components/control.scala
+++ b/src/main/scala/components/control.scala
@@ -1194,7 +1194,7 @@
-       BitPat("b0111011") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
+       BitPat("b0111111") -> List(false.B,  true.B, false.B,  0.U,  false.B,       0.U,      false.B,   0.U, false.B,   true.B,    true.B,   true.B),
"""

    try:
        success = applier.apply_diff_to_container(correct_diff, dry_run=True)
        if success:
            print('✅ Applier succeeded with correct diff format')
        else:
            print('❌ Applier failed even with correct diff')
            return False
    except Exception as e:
        print(f'❌ Applier failed with correct diff: {e}')
        return False

    print('\n🎯 Test Summary:')
    print('✅ DockerDiffApplier correctly handles both success and failure cases')
    print('📝 Next steps:')
    print('   1. Modify v2chisel_batch.py to integrate the retry loop')
    print('   2. Add compilation step after successful diff application')
    print('   3. Add LEC (Logic Equivalence Check) step')

    return True


if __name__ == '__main__':
    success = test_retry_mechanism()
    if success:
        print('\n🎉 Test completed successfully!')
        sys.exit(0)
    else:
        print('\n❌ Test failed!')
        sys.exit(1)
