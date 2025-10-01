package dinocpu

import chisel3._

/**
 * Main control unit for the CPU.
 *
 * This module decodes instructions and generates control signals.
 */
class Control extends Module {
  val io = IO(new Bundle {
    val opcode = Input(UInt(7.W))

    // Control signals
    val branch = Output(Bool())
    val memread = Output(Bool())
    val memwrite = Output(Bool())
    val regwrite = Output(Bool())
    val alusrc = Output(Bool())
    val memtoreg = Output(Bool())
  })

  // Default values
  io.branch := false.B
  io.memread := false.B
  io.memwrite := false.B
  io.regwrite := false.B
  io.alusrc := false.B
  io.memtoreg := false.B

  // R-type instructions
  when(io.opcode === "b0110011".U) {
    io.regwrite := true.B
  }

  // I-type (immediate) instructions
  .elsewhen(io.opcode === "b0010011".U) {
    io.regwrite := true.B
    io.alusrc := true.B
  }

  // Load instructions
  .elsewhen(io.opcode === "b0000011".U) {
    io.memread := true.B
    io.regwrite := true.B
    io.alusrc := true.B
    io.memtoreg := true.B
  }

  // Store instructions
  .elsewhen(io.opcode === "b0100011".U) {
    io.memwrite := true.B
    io.alusrc := true.B
  }

  // Branch instructions
  .elsewhen(io.opcode === "b1100011".U) {
    io.branch := true.B
  }
}

/**
 * Helper object for instantiating Control.
 */
object Control {
  def apply(): Control = new Control()
}

/**
 * Nested decoder for testing nested class detection.
 */
class InstructionDecoder extends Module {
  val io = IO(new Bundle {
    val instruction = Input(UInt(32.W))
    val opcode = Output(UInt(7.W))
    val funct3 = Output(UInt(3.W))
    val funct7 = Output(UInt(7.W))
  })

  io.opcode := io.instruction(6, 0)
  io.funct3 := io.instruction(14, 12)
  io.funct7 := io.instruction(31, 25)
}