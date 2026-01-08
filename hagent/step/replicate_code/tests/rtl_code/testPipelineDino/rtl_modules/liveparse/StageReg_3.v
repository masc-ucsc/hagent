






























module StageReg_3(clock, reset, io_in_ex_result, io_in_mem_writedata, io_in_nextpc, io_in_taken, io_in_instruction, io_flush, io_data_ex_result, io_data_mem_writedata, io_data_nextpc, io_data_taken, io_data_instruction);
reg \$auto$verilog_backend.cc:2355:dump_module$467 = 0;

reg [63:0] _0_;

reg [63:0] _1_;

reg [63:0] _2_;

reg [63:0] _3_;

reg _4_;

wire [63:0] _RAND_0;

wire [63:0] _RAND_1;

wire [63:0] _RAND_2;

wire [31:0] _RAND_3;

wire [63:0] _RAND_4;

input clock;
wire clock;

output [63:0] io_data_ex_result;
wire [63:0] io_data_ex_result;

output [63:0] io_data_instruction;
wire [63:0] io_data_instruction;

output [63:0] io_data_mem_writedata;
wire [63:0] io_data_mem_writedata;

output [63:0] io_data_nextpc;
wire [63:0] io_data_nextpc;

output io_data_taken;
wire io_data_taken;

input io_flush;
wire io_flush;

input [63:0] io_in_ex_result;
wire [63:0] io_in_ex_result;

input [63:0] io_in_instruction;
wire [63:0] io_in_instruction;

input [63:0] io_in_mem_writedata;
wire [63:0] io_in_mem_writedata;

input [63:0] io_in_nextpc;
wire [63:0] io_in_nextpc;

input io_in_taken;
wire io_in_taken;

reg [63:0] reg_ex_result;

reg [63:0] reg_instruction;

reg [63:0] reg_mem_writedata;

reg [63:0] reg_nextpc;

reg reg_taken;

input reset;
wire reset;
always @* begin
if (\$auto$verilog_backend.cc:2355:dump_module$467 ) begin end
_0_ = reg_ex_result;
_1_ = reg_instruction;
_2_ = reg_mem_writedata;
_3_ = reg_nextpc;
_4_ = reg_taken;

if (reset) begin
_0_ = 64'h0000000000000000;
end else begin

if (io_flush) begin
_0_ = 64'h0000000000000000;
end else begin
_0_ = io_in_ex_result;
end
end

if (reset) begin
_2_ = 64'h0000000000000000;
end else begin

if (io_flush) begin
_2_ = 64'h0000000000000000;
end else begin
_2_ = io_in_mem_writedata;
end
end

if (reset) begin
_3_ = 64'h0000000000000000;
end else begin

if (io_flush) begin
_3_ = 64'h0000000000000000;
end else begin
_3_ = io_in_nextpc;
end
end

if (reset) begin
_4_ = 1'h0;
end else begin

if (io_flush) begin
_4_ = 1'h0;
end else begin
_4_ = io_in_taken;
end
end

if (reset) begin
_1_ = 64'h0000000000000000;
end else begin

if (io_flush) begin
_1_ = 64'h0000000000000000;
end else begin
_1_ = io_in_instruction;
end
end
end
always @(posedge clock) begin
reg_ex_result <= _0_;
reg_instruction <= _1_;
reg_mem_writedata <= _2_;
reg_nextpc <= _3_;
reg_taken <= _4_;
end
assign io_data_ex_result = reg_ex_result;
assign io_data_mem_writedata = reg_mem_writedata;
assign io_data_nextpc = reg_nextpc;
assign io_data_taken = reg_taken;
assign io_data_instruction = reg_instruction;
endmodule