package chisel3.test

import chisel3._
import chisel3.util._

class Adder extends Module {
  val io = IO(new Bundle {
    val a = Input(UInt(8.W))
    val b = Input(UInt(8.W))
    val c = Output(UInt(11.W))
  })
  
  io.c := io.a - io.b  // This line should be found by module_finder
}

class Alu extends Module {
  val io = IO(new Bundle {
    val in_valid = Input(Bool())
    val out_valid = Output(Bool())
  })
  
  io.out_valid := io.in_valid  // This line should be found
}