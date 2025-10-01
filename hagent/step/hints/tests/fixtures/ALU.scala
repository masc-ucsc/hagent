package dinocpu

import chisel3._
import chisel3.util._

/**
 * Simple ALU for arithmetic and logic operations.
 */
class ALU extends Module {
  val io = IO(new Bundle {
    val operation = Input(UInt(4.W))
    val inputx = Input(UInt(32.W))
    val inputy = Input(UInt(32.W))
    val result = Output(UInt(32.W))
  })

  // Default output
  io.result := 0.U

  // Decode operation
  switch(io.operation) {
    is("b0000".U) {
      // ADD
      io.result := io.inputx + io.inputy
    }
    is("b0001".U) {
      // SUB
      io.result := io.inputx - io.inputy
    }
    is("b0010".U) {
      // AND
      io.result := io.inputx & io.inputy
    }
    is("b0011".U) {
      // OR
      io.result := io.inputx | io.inputy
    }
    is("b0100".U) {
      // XOR
      io.result := io.inputx ^ io.inputy
    }
    is("b0101".U) {
      // SLT (set less than)
      io.result := (io.inputx.asSInt < io.inputy.asSInt).asUInt
    }
    is("b0110".U) {
      // SLL (shift left logical)
      io.result := io.inputx << io.inputy(4, 0)
    }
    is("b0111".U) {
      // SRL (shift right logical)
      io.result := io.inputx >> io.inputy(4, 0)
    }
  }
}

object ALU {
  def apply(): ALU = {
    new ALU()
  }
}