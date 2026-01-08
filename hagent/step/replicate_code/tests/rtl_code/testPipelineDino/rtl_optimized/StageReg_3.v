module StageReg_3(
  input         clock,
  input         reset,
  input  [63:0] io_in_ex_result,
  input  [63:0] io_in_mem_writedata,
  input  [63:0] io_in_nextpc,
  input         io_in_taken,
  input  [63:0] io_in_instruction,
  input         io_flush,
  output [63:0] io_data_ex_result,
  output [63:0] io_data_mem_writedata,
  output [63:0] io_data_nextpc,
  output        io_data_taken,
  output [63:0] io_data_instruction
);

  // Synchronous registers
  reg [63:0] reg_ex_result;
  reg [63:0] reg_mem_writedata;
  reg [63:0] reg_nextpc;
  reg        reg_taken;
  reg [63:0] reg_instruction;

  // Use separated always blocks for each register

  // reg_ex_result update
  always @(posedge clock) begin
    if (reset)
      reg_ex_result <= 64'h0000000000000000;
    else if (io_flush)
      reg_ex_result <= 64'h0000000000000000;
    else
      reg_ex_result <= io_in_ex_result;
  end

  // reg_mem_writedata update
  always @(posedge clock) begin
    if (reset)
      reg_mem_writedata <= 64'h0000000000000000;
    else if (io_flush)
      reg_mem_writedata <= 64'h0000000000000000;
    else
      reg_mem_writedata <= io_in_mem_writedata;
  end

  // reg_nextpc update
  always @(posedge clock) begin
    if (reset)
      reg_nextpc <= 64'h0000000000000000;
    else if (io_flush)
      reg_nextpc <= 64'h0000000000000000;
    else
      reg_nextpc <= io_in_nextpc;
  end

  // reg_taken update
  always @(posedge clock) begin
    if (reset)
      reg_taken <= 1'h0;
    else if (io_flush)
      reg_taken <= 1'h0;
    else
      reg_taken <= io_in_taken;
  end

  // reg_instruction update
  always @(posedge clock) begin
    if (reset)
      reg_instruction <= 64'h0000000000000000;
    else if (io_flush)
      reg_instruction <= 64'h0000000000000000;
    else
      reg_instruction <= io_in_instruction;
  end

  // Drive the outputs using the registered values.
  assign io_data_ex_result     = reg_ex_result;
  assign io_data_mem_writedata = reg_mem_writedata;
  assign io_data_nextpc        = reg_nextpc;
  assign io_data_taken         = reg_taken;
  assign io_data_instruction   = reg_instruction;

endmodule
