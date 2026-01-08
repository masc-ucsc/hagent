


































module StageReg_5(clock, reset, io_in_readdata, io_in_ex_result, io_in_instruction, io_data_readdata, io_data_ex_result, io_data_instruction);
reg \$auto$verilog_backend.cc:2355:dump_module$469 = 0;

reg [63:0] _0_;

reg [63:0] _1_;

reg [63:0] _2_;

wire [63:0] _RAND_0;

wire [63:0] _RAND_1;

wire [63:0] _RAND_2;

input clock;
wire clock;

output [63:0] io_data_ex_result;
wire [63:0] io_data_ex_result;

output [63:0] io_data_instruction;
wire [63:0] io_data_instruction;

output [63:0] io_data_readdata;
wire [63:0] io_data_readdata;

input [63:0] io_in_ex_result;
wire [63:0] io_in_ex_result;

input [63:0] io_in_instruction;
wire [63:0] io_in_instruction;

input [63:0] io_in_readdata;
wire [63:0] io_in_readdata;

reg [63:0] reg_ex_result;

reg [63:0] reg_instruction;

reg [63:0] reg_readdata;

input reset;
wire reset;
always @* begin
if (\$auto$verilog_backend.cc:2355:dump_module$469 ) begin end
_2_ = reg_readdata;
_0_ = reg_ex_result;
_1_ = reg_instruction;

if (reset) begin
_2_ = 64'h0000000000000000;
end else begin
_2_ = io_in_readdata;
end

if (reset) begin
_0_ = 64'h0000000000000000;
end else begin
_0_ = io_in_ex_result;
end

if (reset) begin
_1_ = 64'h0000000000000000;
end else begin
_1_ = io_in_instruction;
end
end
always @(posedge clock) begin
reg_readdata <= _2_;
reg_ex_result <= _0_;
reg_instruction <= _1_;
end
assign io_data_readdata = reg_readdata;
assign io_data_ex_result = reg_ex_result;
assign io_data_instruction = reg_instruction;
endmodule