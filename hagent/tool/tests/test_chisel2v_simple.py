#!/usr/bin/env python3
"""
Example usage of the Chisel2v tool.

This script shows how one might invoke the Chisel2v class to convert
a Chisel module (given as a string) into Verilog.
"""

import sys
from hagent.tool.chisel2v import Chisel2v


def main():
    # A minimal Chisel module:
    chisel_code = r"""
import chisel3._

class MyModule extends Module {
  val io = IO(new Bundle {
    val in = Input(UInt(2.W))
    val out = Output(UInt(32.W))
  })
  val instrMem = VecInit(Seq(
    "h00400093".U(32.W), // addi x1, x0, 4   -> x1 = 4
    "h00A08113".U(32.W), // addi x2, x1, 10  -> x2 = x1 + 10
    "h00208233".U(32.W), // add  x4, x1, x2  -> x4 = x1 + x2
    "h01000063".U(32.W)  // branch instruction (opcode 1100011)
  ))
  io.out := instrMem(io.in)
}
"""

    # Create the tool instance
    c2v = Chisel2v()

    # Attempt setup with a path to sbt, or None if it's in the system PATH
    if not c2v.setup(sbt_path=None):
        print('Setup failed:', c2v.error_message, file=sys.stderr)
        sys.exit(1)

    # Generate Verilog
    try:
        txt = c2v.generate_verilog(chisel_code, 'MyModule')
        print(f'Successfully generated:\n{txt}')
    except RuntimeError as e:
        print(f'Verilog generation failed: {e}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
