
























module StageReg(clock, reset, io_in_instruction, io_in_pc, io_flush, io_valid, io_data_instruction, io_data_pc);
reg \$auto$verilog_backend.cc:2355:dump_module$464 = 0;

reg [31:0] _0_;

reg [63:0] _1_;

wire [31:0] _RAND_0;

wire [63:0] _RAND_1;

input clock;
wire clock;

output [31:0] io_data_instruction;
wire [31:0] io_data_instruction;

output [63:0] io_data_pc;
wire [63:0] io_data_pc;

input io_flush;
wire io_flush;

input [31:0] io_in_instruction;
wire [31:0] io_in_instruction;

input [63:0] io_in_pc;
wire [63:0] io_in_pc;

input io_valid;
wire io_valid;

reg [31:0] reg_instruction;

reg [63:0] reg_pc;

input reset;
wire reset;
always @* begin
if (\$auto$verilog_backend.cc:2355:dump_module$464 ) begin end
_0_ = reg_instruction;
_1_ = reg_pc;

if (reset) begin
_0_ = 32'd0;
end else begin

if (io_flush) begin
_0_ = 32'd0;
end else begin

if (io_valid) begin
_0_ = io_in_instruction;
end else begin
end
end
end

if (reset) begin
_1_ = 64'h0000000000000000;
end else begin

if (io_flush) begin
_1_ = 64'h0000000000000000;
end else begin

if (io_valid) begin
_1_ = io_in_pc;
end else begin
end
end
end
end
always @(posedge clock) begin
reg_instruction <= _0_;
reg_pc <= _1_;
end
assign io_data_instruction = reg_instruction;
assign io_data_pc = reg_pc;
endmodule