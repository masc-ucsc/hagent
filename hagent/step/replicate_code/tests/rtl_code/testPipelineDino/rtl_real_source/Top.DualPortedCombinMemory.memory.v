module BindsTo_0_DualPortedCombinMemory(
  input         clock,
  input         reset,
  input         io_imem_request_valid,
  input  [63:0] io_imem_request_bits_address,
  output [63:0] io_imem_response_bits_data,
  input         io_dmem_request_valid,
  input  [63:0] io_dmem_request_bits_address,
  input  [63:0] io_dmem_request_bits_writedata,
  input  [1:0]  io_dmem_request_bits_operation,
  output        io_dmem_response_valid,
  output [63:0] io_dmem_response_bits_data
);

initial begin
  $readmemh("test", DualPortedCombinMemory.memory);
end
                      endmodule

bind DualPortedCombinMemory BindsTo_0_DualPortedCombinMemory BindsTo_0_DualPortedCombinMemory_Inst(.*);