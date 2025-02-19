// Import Chisel library
//
import chisel3._
import chisel3.util._

// Define the Counter module
class Counter extends Module {
  val io = IO(new Bundle {
    val enable = Input(Bool())
    val reset  = Input(Bool())
    val count  = Output(UInt(4.W))
  })

  // Initialize the count register
  val countReg = RegInit(0.U(4.W))

  when (io.reset) {
    countReg := 0.U
  } .elsewhen (io.enable) {
    countReg := countReg + 1.U
  }

  // Connect the count register to the output
  io.count := countReg
}

// Generate the Verilog code
object CounterDriver extends App {
  emitVerilog(new Counter())
}
