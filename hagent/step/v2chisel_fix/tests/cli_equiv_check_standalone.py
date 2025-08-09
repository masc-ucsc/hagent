#!/usr/bin/env python3
# See LICENSE for details
"""
Demonstration of using Equiv_check in-code to verify equivalence
of two Verilog snippets read from a YAML input file.
After checking, the script adds a field "lec" with value 1 if the designs
are equivalent, or 0 otherwise.

Usage:
  uv run python3 hagent/step/v2chisel_fix/tests/cli_equiv_check_standalone.py input.yaml

Or run with pytest:
  uv run pytest hagent/step/v2chisel_fix/tests/cli_equiv_check_standalone.py
"""

import sys
from pathlib import Path
from ruamel.yaml import YAML
from hagent.tool.equiv_check import Equiv_check


def load_yaml_data(input_file: str) -> dict:
    """Load and parse YAML data from file."""
    yaml = YAML()
    yaml.indent(mapping=2, sequence=4, offset=2)

    with open(input_file, 'r') as f:
        data = yaml.load(f)
    return data


def extract_verilog_codes(data: dict) -> tuple[str, str]:
    """Extract gold and gate Verilog codes from YAML data."""
    # Get gate_code from either the top-level key or from nested chisel_pass1
    if 'verilog_candidate' in data:
        gate_code = data['verilog_candidate']
    elif 'chisel_pass1' in data and 'verilog_candidate' in data['chisel_pass1']:
        gate_code = data['chisel_pass1']['verilog_candidate']
    else:
        gate_code = ''

    # Use 'verilog_fixed' as gold_code
    gold_code = data.get('verilog_fixed', '')

    if not gate_code or not gold_code:
        raise ValueError("Input YAML must contain keys 'verilog_candidate' and 'verilog_fixed'.")

    return gold_code, gate_code


def run_equivalence_check(gold_code: str, gate_code: str) -> tuple[bool, str, str]:
    """Run equivalence check and return (result, error_msg, counterexample_str)."""
    # Instantiate the equivalence checker
    checker = Equiv_check()

    # Setup: check if Yosys is accessible
    ok = checker.setup()
    if not ok:
        raise RuntimeError(f'Equiv_check setup failed: {checker.get_error()}')

    # Run the equivalence check
    result = checker.check_equivalence(gold_code, gate_code)
    error_msg = checker.get_error()
    counterexample_str = checker.get_counterexample() or ''

    return result, error_msg, counterexample_str


def test_counter_out_fix_equivalence():
    """Test that counter_out_fix.yaml designs are equivalent."""
    # Get the path to the test YAML file (same directory as this script)
    current_dir = Path(__file__).parent
    yaml_file = current_dir / 'counter_out_fix.yaml'

    # Load test data
    data = load_yaml_data(str(yaml_file))

    # Extract Verilog codes
    gold_code, gate_code = extract_verilog_codes(data)

    # Run equivalence check
    result, error_msg, counterexample_str = run_equivalence_check(gold_code, gate_code)

    # This test case should have equivalent designs
    assert result is True, f'counter_out_fix.yaml should have equivalent designs but got result={result}, error={error_msg}'

    # Should not have counterexample information when equivalent
    assert not counterexample_str, 'Should not have counterexample information when designs are equivalent'

    print('✓ Counter designs in counter_out_fix.yaml are equivalent as expected')


def test_counter_out_badfix_non_equivalence():
    """Test that counter_out_badfix.yaml designs are non-equivalent."""
    # Get the path to the test YAML file (same directory as this script)
    current_dir = Path(__file__).parent
    yaml_file = current_dir / 'counter_out_badfix.yaml'

    # Load test data
    data = load_yaml_data(str(yaml_file))

    # Extract Verilog codes
    gold_code, gate_code = extract_verilog_codes(data)

    # Run equivalence check
    result, error_msg, counterexample_str = run_equivalence_check(gold_code, gate_code)

    # This test case should have non-equivalent designs
    assert result is False, (
        f'counter_out_badfix.yaml should have non-equivalent designs but got result={result}, error={error_msg}'
    )

    # Should have counterexample information when non-equivalent
    assert counterexample_str, 'Should have counterexample information when designs are non-equivalent'

    print('✓ Counter designs in counter_out_badfix.yaml are non-equivalent as expected')
    print(f'✓ Counterexample provided: {len(counterexample_str)} characters')


def test_module_name_difference():
    """Test that our code can handle modules with different names using the equivalent test case."""
    # Get the path to the equivalent test YAML file
    current_dir = Path(__file__).parent
    yaml_file = current_dir / 'counter_out_fix.yaml'

    data = load_yaml_data(str(yaml_file))
    gold_code, gate_code = extract_verilog_codes(data)

    # Extract module names to verify they are different
    import re

    gold_match = re.search(r'module\s+([A-Za-z0-9_]+)', gold_code)
    gate_match = re.search(r'module\s+([A-Za-z0-9_]+)', gate_code)

    assert gold_match and gate_match, 'Should find module definitions in both codes'

    gold_module = gold_match.group(1)
    gate_module = gate_match.group(1)

    # The test case should have different module names
    print(f'Gold module: {gold_module}, Gate module: {gate_module}')

    # Run equivalence check even with different names
    result, error_msg, counterexample_str = run_equivalence_check(gold_code, gate_code)

    # Should successfully complete and find equivalence despite different names
    assert result is True, (
        f'Should handle different module names and find equivalence, but got result={result}, error={error_msg}'
    )

    print(f'✓ Successfully handled modules with different names: {gold_module} vs {gate_module}')
    print(f'✓ Equivalence result: {result} (equivalent despite different names)')


def main():
    if len(sys.argv) < 2:
        print(f'Usage: {sys.argv[0]} input.yaml')
        sys.exit(1)

    input_file = sys.argv[1]
    yaml = YAML()
    yaml.indent(mapping=2, sequence=4, offset=2)

    try:
        # Load YAML data
        data = load_yaml_data(input_file)

        # Extract Verilog codes
        gold_code, gate_code = extract_verilog_codes(data)

        # Run equivalence check
        result, error_msg, counterexample = run_equivalence_check(gold_code, gate_code)

    except Exception as e:
        print(f'Error during equivalence check: {e}')
        sys.exit(1)

    # Interpret the result and decide lec value
    if result is True:
        print('Designs are equivalent.')
        lec_val = 1
    elif result is False:
        print('Designs are NOT equivalent.')
        lec_val = 0
        # Show counterexample if available
        if counterexample:
            print('Found counterexample:')
            print(counterexample)
    else:
        # Inconclusive
        print('Equivalence check inconclusive.')
        print(f'Error message: {error_msg}')
        lec_val = 0

    # Add new field "lec" to the YAML data without modifying other fields
    data['lec'] = lec_val

    # Write the updated YAML back to the same file
    try:
        with open(input_file, 'w') as f:
            yaml.dump(data, f)
    except Exception as e:
        print(f"Error writing YAML file '{input_file}': {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
