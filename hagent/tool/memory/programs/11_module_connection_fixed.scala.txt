import chisel3._

class Adder extends Module {
  val io = IO(new Bundle {
    val a = Input(UInt(8.W))
    val b = Input(UInt(8.W))
    val sum = Output(UInt(8.W))
  })
  
  val result = io.a + io.b
  
  // Fixed: Added connection to output
  io.sum := result
}

object AdderMain extends App {
  chisel3.stage.ChiselStage.emitVerilog(new Adder)
} 