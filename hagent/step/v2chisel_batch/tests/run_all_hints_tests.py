#!/usr/bin/env python3
"""
Comprehensive test runner for HintsGenerator integration.

This script runs all HintsGenerator tests in the correct order and provides
detailed reporting of the results.

Usage:
    uv run python hagent/step/v2chisel_batch/tests/run_all_hints_tests.py

Or run individual test categories:
    uv run python hagent/step/v2chisel_batch/tests/run_all_hints_tests.py --unit-only
    uv run python hagent/step/v2chisel_batch/tests/run_all_hints_tests.py --integration-only
    uv run python hagent/step/v2chisel_batch/tests/run_all_hints_tests.py --pipeline-only
"""

import argparse
import subprocess
import sys
import os
from pathlib import Path


def run_command(cmd, description):
    """Run a command and return success/failure with output."""
    print(f"\\n{'=' * 60}")
    print(f"🧪 {description}")
    print(f"{'=' * 60}")
    print(f"Command: {' '.join(cmd)}")
    print()
    
    try:
        result = subprocess.run(cmd, capture_output=False, text=True, check=True)
        print(f"\\n✅ {description} - PASSED")
        return True
    except subprocess.CalledProcessError as e:
        print(f"\\n❌ {description} - FAILED")
        print(f"Return code: {e.returncode}")
        return False
    except Exception as e:
        print(f"\\n❌ {description} - ERROR: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(description='Run HintsGenerator tests')
    parser.add_argument('--unit-only', action='store_true', help='Run only unit tests')
    parser.add_argument('--integration-only', action='store_true', help='Run only integration tests')
    parser.add_argument('--pipeline-only', action='store_true', help='Run only pipeline tests')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    # Set up environment
    os.environ['HAGENT_EXECUTION_MODE'] = 'docker'
    
    # Get the base directory
    base_dir = Path(__file__).parent.parent.parent.parent.parent
    os.chdir(base_dir)
    
    print("🔬 HintsGenerator Integration Test Suite")
    print("=" * 80)
    print("This test suite verifies that HintsGenerator is properly integrated")
    print("with v2chisel_batch and maintains all expected functionality.")
    print()
    
    results = []
    
    # Test 1: Unit Tests
    if not args.integration_only and not args.pipeline_only:
        verbose_flag = ['-v'] if args.verbose else []
        success = run_command(
            ['uv', 'run', 'pytest', 'hagent/step/v2chisel_batch/tests/test_hints_generator.py'] + verbose_flag,
            "Unit Tests - HintsGenerator Class"
        )
        results.append(("Unit Tests", success))
    
    # Test 2: Basic Integration
    if not args.unit_only and not args.pipeline_only:
        success = run_command(
            ['uv', 'run', 'python', 'hagent/step/v2chisel_batch/tests/test_hints_generator_integration.py'],
            "Basic Integration - V2chisel_batch Setup"
        )
        results.append(("Basic Integration", success))
    
    # Test 3: End-to-End Integration
    if not args.unit_only and not args.pipeline_only:
        success = run_command(
            ['uv', 'run', 'python', 'hagent/step/v2chisel_batch/tests/test_hints_generator_e2e.py'],
            "End-to-End Integration - Full Workflow"
        )
        results.append(("E2E Integration", success))
    
    # Test 4: Pipeline Integration
    if not args.unit_only and not args.integration_only:
        success = run_command(
            ['uv', 'run', 'python', 'hagent/step/v2chisel_batch/tests/test_hints_generator_pipeline.py'],
            "Pipeline Integration - Real v2chisel_batch Methods"
        )
        results.append(("Pipeline Integration", success))
    
    # Test 5: Backwards Compatibility
    if not args.unit_only:
        print(f"\\n{'=' * 60}")
        print("🧪 Testing Backwards Compatibility")
        print(f"{'=' * 60}")
        
        # Test that existing v2chisel_batch functionality still works
        success = run_command(
            ['uv', 'run', 'python', '-c', '''
import os
os.environ["HAGENT_EXECUTION_MODE"] = "docker"

from hagent.step.v2chisel_batch.v2chisel_batch import V2chisel_batch
from hagent.step.v2chisel_batch.components.bug_info import BugInfo
from hagent.step.v2chisel_batch.components.hints_generator import HintsGenerator

# Test that all imports work
print("✅ All imports successful")

# Test that V2chisel_batch can be created (without setup to avoid file requirements)
processor = V2chisel_batch()
print("✅ V2chisel_batch instance created")

# Test that components can be created independently
from hagent.tool.module_finder import Module_finder
module_finder = Module_finder()
hints_gen = HintsGenerator(module_finder)
print("✅ HintsGenerator can be created independently")

# Test BugInfo integration
bug_data = {"file": "test.sv", "unified_diff": "test diff"}
bug_info = BugInfo(bug_data, 0)
print(f"✅ BugInfo integration: {bug_info.get_display_name()}")

print("\\n🎉 Backwards compatibility confirmed!")
            '''],
            "Backwards Compatibility Check"
        )
        results.append(("Backwards Compatibility", success))
    
    # Report Results
    print(f"\\n{'=' * 80}")
    print("📊 TEST RESULTS SUMMARY")
    print(f"{'=' * 80}")
    
    passed = 0
    failed = 0
    
    for test_name, success in results:
        status = "✅ PASSED" if success else "❌ FAILED"
        print(f"{test_name:.<50} {status}")
        if success:
            passed += 1
        else:
            failed += 1
    
    print(f"\\nTotal Tests: {len(results)}")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    
    if failed == 0:
        print(f"\\n🎉 ALL TESTS PASSED!")
        print("✅ HintsGenerator is fully integrated and working correctly")
        print("✅ Ready for production use")
        sys.exit(0)
    else:
        print(f"\\n❌ {failed} TEST(S) FAILED!")
        print("Please check the output above for details")
        sys.exit(1)


if __name__ == '__main__':
    main()