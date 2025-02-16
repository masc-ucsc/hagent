#!/usr/bin/env python3
# See LICENSE for details
"""
Demonstration of using Equiv_check in-code to verify equivalence
of two Verilog snippets read from a YAML input file.

Usage:
  poetry run python3 hagent/step/test_equiv_check_standalone.py input.yaml
"""

import sys
import yaml
from hagent.tool.equiv_check import Equiv_check

def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} input.yaml")
        sys.exit(1)

    input_file = sys.argv[1]
    try:
        with open(input_file, 'r') as f:
            data = yaml.safe_load(f)
    except Exception as e:
        print(f"Error reading YAML file '{input_file}': {e}")
        sys.exit(1)

    # Try to get gold_code from either the top-level key "verilog_candidate"
    # or from the nested "chisel_pass1" field.
    if "verilog_candidate" in data:
        gold_code = data["verilog_candidate"]
    elif "chisel_pass1" in data and "verilog_candidate" in data["chisel_pass1"]:
        gold_code = data["chisel_pass1"]["verilog_candidate"]
    else:
        gold_code = ""

    # Use 'verilog_fixed' as ref_code.
    ref_code = data.get("verilog_fixed", "")

    if not gold_code or not ref_code:
        print("Input YAML must contain keys 'verilog_candidate' and 'verilog_fixed'.")
        sys.exit(1)

    # Instantiate the checker
    checker = Equiv_check()

    # Setup: check if Yosys is accessible
    ok = checker.setup()
    if not ok:
        print(f'Equiv_check setup failed: {checker.get_error()}')
        return

    # Run the equivalence check
    try:
        result = checker.check_equivalence(gold_code, ref_code)
    except Exception as e:
        print(f'Error during check_equivalence: {e}')
        return

    # Interpret the result
    if result is True:
        print('Designs are equivalent.')
    elif result is False:
        print('Designs are NOT equivalent.')
        cex = checker.get_counterexample()
        if cex:
            print(f'Counterexample: {cex}')
    else:
        # None => unknown or inconclusive
        print('Equivalence check inconclusive.')
        print(f'Error message: {checker.get_error()}')

if __name__ == '__main__':
    main()
