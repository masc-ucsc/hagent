module ForwardingUnit(
  input  [4:0] io_rs1,
  input  [4:0] io_rs2,
  input  [4:0] io_exmemrd,
  input        io_exmemrw,
  input  [4:0] io_memwbrd,
  input        io_memwbrw,
  output reg [1:0] io_forwardA,
  output reg [1:0] io_forwardB
);

  // Intermediate signals computed in a first combinational stage.
  reg ex_fwd_A;
  reg mem_fwd_A;
  reg ex_fwd_B;
  reg mem_fwd_B;

  always @(*) begin
    // For operand A: check the EX stage and MEM stage conditions.
    ex_fwd_A  = io_exmemrw   && (io_exmemrd == io_rs1) && (io_exmemrd != 5'h00);
    mem_fwd_A = io_memwbrw   && (io_memwbrd == io_rs1) && (io_memwbrd != 5'h00);

    // For operand B: check the EX stage and MEM stage conditions.
    ex_fwd_B  = io_exmemrw   && (io_exmemrd == io_rs2) && (io_exmemrd != 5'h00);
    mem_fwd_B = io_memwbrw   && (io_memwbrd == io_rs2) && (io_memwbrd != 5'h00);
  end

  // Final output logic: the conditions from the previous stage are combined
  // with priority given to the EX stage over the MEM stage.
  always @(*) begin
    if (ex_fwd_A)
      io_forwardA = 2'h1;
    else if (mem_fwd_A)
      io_forwardA = 2'h2;
    else
      io_forwardA = 2'h0;
      
    if (ex_fwd_B)
      io_forwardB = 2'h1;
    else if (mem_fwd_B)
      io_forwardB = 2'h2;
    else
      io_forwardB = 2'h0;
  end

endmodule
