#!/usr/bin/env scala-cli
//> using scala      "2.13.14"
//> using repository "sonatype:releases"
//> using dep       "edu.berkeley.cs::chisel3:3.6.1"
//> using plugin    "edu.berkeley.cs::chisel3-plugin:3.6.1"

import chisel3._

class Adder extends Module {
  val io = IO(new Bundle {
    val a = Input(UInt(8.W))
    val b = Input(UInt(8.W))
    val sum = Output(UInt(8.W))
  })
  
  val result = io.a + io.b
  
  // Bug: Missing connection to output
  io.sum := result
}

object AdderMain extends App {
  chisel3.stage.ChiselStage.emitVerilog(new Adder)
} 