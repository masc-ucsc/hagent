#!/usr/bin/env python3

import sys

from hagent.tool.compile_slang import Compile_slang

def main():
    # Minimal Verilog code to be compiled.
    verilog_code = r"""
module trivial(input [2:0] a, input [2:0] b, output [1:0] c);
wire tmp;  // Warning, undriven
assign c = a ^ tmp; // warning here about conversion
assign x = a[1] ^ b[0] // error here -- Semicolon
endmodule

module leaf5(input [29:0] ci, output [29:0] co);
  assign co = ~ci;
endmodule
"""

    # Create an instance of the Compile_slang tool.
    compiler = Compile_slang()

    # Validate setup: Ensure the pyslang package is present.
    if not compiler.setup():
        print("Setup failed:", compiler.error_message, file=sys.stderr)
        sys.exit(1)

    compiler.add_source(text=verilog_code)

    if compiler.set_top("potato"):
        print("Potato should not be a valid top", file=sys.stderr)
        sys.exit(1)

    hierarchy = compiler.get_hierarchy()
    assert len(hierarchy) == 2
    sum('trivial' in s for s in hierarchy)
    sum('leaf5' in s for s in hierarchy)

    # Not needed to set trivial if there is a single module
    if not compiler.set_top("trivial"):
        print("Failed to set trivial as top module.", file=sys.stderr)
        sys.exit(1)

    hierarchy = compiler.get_hierarchy()
    assert len(hierarchy) == 1
    assert hierarchy[0] == "trivial"

    # Retrieve input/output definitions from the top module.
    ios = compiler.get_ios()
    assert len(ios) == 3
    assert ios[0].name == "a"
    assert ios[1].name == "b"
    assert ios[2].name == "c"

    assert ios[0].input == True
    assert ios[1].input == True
    assert ios[2].input == False

    assert ios[0].output == False
    assert ios[1].output == False
    assert ios[2].output == True

    assert ios[0].bits == 3
    assert ios[1].bits == 3
    assert ios[2].bits == 2

    # Retrieve compilation warnings and errors.
    warnings = compiler.get_warnings()
    errors = compiler.get_errors()
    assert len(warnings)>2
    assert len(errors)==1
    assert errors[0].loc > 0


if __name__ == "__main__":
    main()

