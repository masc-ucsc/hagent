`timescale 1ns/1ps

// Testbench skeleton for conv_mac
// - Generates clock and reset
// - Instantiates DUT with default parameters
// - Leaves stimulus commented out for MCP/AI to generate later

module conv_mac_tb;

  // Parameters
  localparam int WIDTH     = 8;
  localparam int ACC_WIDTH = 32;

  // Clock and reset
  reg clk;
  reg rst_n;

  // Inputs
  reg                 in_valid;
  reg                 in_first;
  reg                 in_last;
  reg  [WIDTH-1:0]    a_in;
  reg  [WIDTH-1:0]    b_in;
  reg                 bias_valid;
  reg  [ACC_WIDTH-1:0] bias_in;

  // Outputs
  wire                out_valid;
  wire [ACC_WIDTH-1:0] out_sum;

  // Clock generation: 100MHz equivalent (10ns period)
  initial clk = 1'b0;
  always #5 clk = ~clk;

  // DUT instantiation
  conv_mac #(
    .WIDTH(WIDTH),
    .ACC_WIDTH(ACC_WIDTH),
    .SIGNED_MUL(1'b1)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .in_valid(in_valid),
    .in_first(in_first),
    .in_last(in_last),
    .a_in(a_in),
    .b_in(b_in),
    .bias_valid(bias_valid),
    .bias_in(bias_in),
    .out_valid(out_valid),
    .out_sum(out_sum)
  );

  // Reset and default initialization
  initial begin
    rst_n      = 1'b0;
    in_valid   = 1'b0;
    in_first   = 1'b0;
    in_last    = 1'b0;
    a_in       = '0;
    b_in       = '0;
    bias_valid = 1'b0;
    bias_in    = '0;

    // Hold reset for a few cycles
    repeat (5) @(posedge clk);
    rst_n = 1'b1;

    // NOTE: Stimulus intentionally left commented for MCP/AI generation
    // Example (to be replaced by MCP):
    // send_window(4, '{8'd1, 8'd2, 8'd3, 8'd4}, '{8'd5, 8'd6, 8'd7, 8'd8});

    // Run for some time then finish
    repeat (200) @(posedge clk);
    $display("conv_mac_tb: Completed placeholder run");
    $finish;
  end

  // Optional: simple monitor
  initial begin
    $display("Time  rst_n  valid  first last  a    b    bias_v out_v sum");
    forever begin
      @(posedge clk);
      $display("%0t   %0b      %0b      %0b    %0b   %0d   %0d   %0b     %0b   %0d",
               $time, rst_n, in_valid, in_first, in_last, a_in, b_in, bias_valid, out_valid, out_sum);
    end
  end

  // Task placeholder (to be completed by MCP)
  // task automatic send_window(input int n, input logic [WIDTH-1:0] a_vec[], input logic [WIDTH-1:0] b_vec[]);
  // endtask

endmodule


