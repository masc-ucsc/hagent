#!/usr/bin/env python3
# See LICENSE for details
"""
Demonstration of using Equiv_check in-code to verify equivalence
of two Verilog snippets read from a YAML input file.
After checking, the script adds a field "lec" with value 1 if the designs
are equivalent, or 0 otherwise.

Usage:
  uv run python3 hagent/step/test_equiv_check_standalone.py input.yaml
"""

import sys
from ruamel.yaml import YAML
from hagent.tool.equiv_check import Equiv_check
from typing import List, Tuple


def main():
    if len(sys.argv) < 2:
        print(f'Usage: {sys.argv[0]} input.yaml')
        sys.exit(1)

    input_file = sys.argv[1]
    yaml = YAML()
    # Optional: adjust indentation
    yaml.indent(mapping=2, sequence=4, offset=2)

    try:
        with open(input_file, 'r') as f:
            data = yaml.load(f)
    except Exception as e:
        print(f"Error reading YAML file '{input_file}': {e}")
        sys.exit(1)

    # Get gold_code from either the top-level key or from nested chisel_pass1
    if 'verilog_candidate' in data:
        gate_code = data['verilog_candidate']
    elif 'chisel_pass1' in data and 'verilog_candidate' in data['chisel_pass1']:
        gate_code = data['chisel_pass1']['verilog_candidate']
    else:
        gate_code = ''

    # Use 'verilog_fixed' as ref_code.
    gold_code = data.get('verilog_fixed', '')

    if not gate_code or not gold_code:
        print("Input YAML must contain keys 'verilog_candidate' and 'verilog_fixed'.")
        sys.exit(1)

    # Instantiate the equivalence checker
    checker = Equiv_check()

    # Setup: check if Yosys is accessible
    ok = checker.setup()
    if not ok:
        print(f'Equiv_check setup failed: {checker.get_error()}')
        sys.exit(1)

    # Run the equivalence check
    try:
        result = checker.check_equivalence(gold_code, gate_code)
    except Exception as e:
        print(f'Error during check_equivalence: {e}')
        sys.exit(1)

    # Interpret the result and decide lec value
    if result is True:
        print('Designs are equivalent.')
        lec_val = 1
    elif result is False:
        print('Designs are NOT equivalent.')
        lec_val = 0
        # Retrieve list of (module, io_name) tuples
        cex_list: List[Tuple[str, str]] = checker.get_counterexample() or []
        if cex_list:
            print('Found mismatches in the following signals:')
            for module_name, io_name in cex_list:
                print(f'  • Module "{module_name}", IO "{io_name}"')
    else:
        # Inconclusive
        print('Equivalence check inconclusive.')
        print(f'Error message: {checker.get_error()}')
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
