#!/usr/bin/env python3
# See LICENSE for details
"""
Demonstration of using Equiv_check in-code to verify equivalence
of two identical Verilog snippets.

usage:
poetry run python3 hagent/step/test_equiv_check_standalone.py
"""

from hagent.tool.equiv_check import Equiv_check


def main():
    # Two identical verilog modules named 'top'
    gold_code = """
module top(output x,input a);
    assign x = a;
endmodule
"""
    ref_code = """
module top(output x,input a);
    assign x = a;
endmodule
"""

    # Instantiate the checker
    checker = Equiv_check()

    # Setup: checks if Yosys is accessible
    # If Yosys is not in PATH or not installed, this returns False
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
