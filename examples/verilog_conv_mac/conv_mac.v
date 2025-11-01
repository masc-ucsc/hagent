// Convolution MAC (Multiply-Accumulate) — 2-stage pipeline, streaming windows.
// - Computes dot product: sum_{i=0..(N-1)} a[i] * b[i]
// - Windows are delimited by in_first/in_last flags in the input stream.
// - out_valid pulses exactly once per window with the final accumulated sum.
// - Latency: 2 cycles from the corresponding input cycle.
// NOTE: This file defines only the interface; implementation will be AI-generated via MCP.

`timescale 1ns/1ps
module conv_mac #(
  parameter int WIDTH      = 8,      // element bit-width for a/b
  parameter int ACC_WIDTH  = 32,     // accumulator/output bit-width
  parameter bit SIGNED_MUL = 1'b1    // 1: interpret a,b as signed; 0: unsigned
) (
  input  logic                 clk,
  input  logic                 rst_n,       // async active-low reset

  // Input stream (always-ready in this base version):
  input  logic                 in_valid,    // high when a_in/b_in are valid
  input  logic                 in_first,    // high with the first pair of a window
  input  logic                 in_last,     // high with the last  pair of a window
  input  logic [WIDTH-1:0]     a_in,
  input  logic [WIDTH-1:0]     b_in,

  // Optional bias (applied once at window start when bias_valid && in_first)
  input  logic                 bias_valid,  // tie-low if unused
  input  logic [ACC_WIDTH-1:0] bias_in,     // tie-zero if unused

  // Output (one result per input window):
  output logic                 out_valid,   // pulses for exactly 1 cycle per window
  output logic [ACC_WIDTH-1:0] out_sum
);

  // Implementation goes here (student task / MCP-generated).

endmodule


