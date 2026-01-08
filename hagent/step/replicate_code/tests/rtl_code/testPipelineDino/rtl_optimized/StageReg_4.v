
































module StageReg_4(clock, reset, io_in_mem_ctrl_memop, io_in_wb_ctrl_toreg, io_in_wb_ctrl_regwrite, io_flush, io_data_mem_ctrl_memop, io_data_wb_ctrl_toreg, io_data_wb_ctrl_regwrite);
reg \$auto$verilog_backend.cc:2355:dump_module$468 = 0;

reg [1:0] _0_;

reg _1_;

reg _2_;

wire [31:0] _RAND_0;

wire [31:0] _RAND_1;

wire [31:0] _RAND_2;

input clock;
wire clock;

output [1:0] io_data_mem_ctrl_memop;
wire [1:0] io_data_mem_ctrl_memop;

output io_data_wb_ctrl_regwrite;
wire io_data_wb_ctrl_regwrite;

output io_data_wb_ctrl_toreg;
wire io_data_wb_ctrl_toreg;

input io_flush;
wire io_flush;

input [1:0] io_in_mem_ctrl_memop;
wire [1:0] io_in_mem_ctrl_memop;

input io_in_wb_ctrl_regwrite;
wire io_in_wb_ctrl_regwrite;

input io_in_wb_ctrl_toreg;
wire io_in_wb_ctrl_toreg;

reg [1:0] reg_mem_ctrl_memop;

reg reg_wb_ctrl_regwrite;

reg reg_wb_ctrl_toreg;

input reset;
wire reset;
always @* begin
if (\$auto$verilog_backend.cc:2355:dump_module$468 ) begin end
_2_ = reg_wb_ctrl_toreg;
_1_ = reg_wb_ctrl_regwrite;
_0_ = reg_mem_ctrl_memop;

if (reset) begin
_0_ = 2'h0;
end else begin

if (io_flush) begin
_0_ = 2'h0;
end else begin
_0_ = io_in_mem_ctrl_memop;
end
end

if (reset) begin
_2_ = 1'h0;
end else begin

if (io_flush) begin
_2_ = 1'h0;
end else begin
_2_ = io_in_wb_ctrl_toreg;
end
end

if (reset) begin
_1_ = 1'h0;
end else begin

if (io_flush) begin
_1_ = 1'h0;
end else begin
_1_ = io_in_wb_ctrl_regwrite;
end
end
end
always @(posedge clock) begin
reg_wb_ctrl_toreg <= _2_;
reg_wb_ctrl_regwrite <= _1_;
reg_mem_ctrl_memop <= _0_;
end
assign io_data_mem_ctrl_memop = reg_mem_ctrl_memop;
assign io_data_wb_ctrl_toreg = reg_wb_ctrl_toreg;
assign io_data_wb_ctrl_regwrite = reg_wb_ctrl_regwrite;
endmodule