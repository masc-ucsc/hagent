




























module StageReg_2(clock, reset, io_in_ex_ctrl_itype, io_in_ex_ctrl_aluop, io_in_ex_ctrl_src1, io_in_ex_ctrl_src2, io_in_ex_ctrl_branch, io_in_ex_ctrl_jumptype, io_in_ex_ctrl_resultselect, io_in_ex_ctrl_wordinst, io_in_mem_ctrl_memop, io_in_wb_ctrl_toreg, io_in_wb_ctrl_regwrite, io_flush, io_data_ex_ctrl_itype, io_data_ex_ctrl_aluop, io_data_ex_ctrl_src1, io_data_ex_ctrl_src2, io_data_ex_ctrl_branch, io_data_ex_ctrl_jumptype, io_data_ex_ctrl_resultselect
, io_data_ex_ctrl_wordinst, io_data_mem_ctrl_memop, io_data_wb_ctrl_toreg, io_data_wb_ctrl_regwrite);
reg \$auto$verilog_backend.cc:2355:dump_module$466 = 0;

reg _00_;

reg _01_;

reg _02_;

reg [1:0] _03_;

reg _04_;

reg _05_;

reg [1:0] _06_;

reg _07_;

reg [1:0] _08_;

reg _09_;

reg _10_;

wire [31:0] _RAND_0;

wire [31:0] _RAND_1;

wire [31:0] _RAND_10;

wire [31:0] _RAND_2;

wire [31:0] _RAND_3;

wire [31:0] _RAND_4;

wire [31:0] _RAND_5;

wire [31:0] _RAND_6;

wire [31:0] _RAND_7;

wire [31:0] _RAND_8;

wire [31:0] _RAND_9;

input clock;
wire clock;

output io_data_ex_ctrl_aluop;
wire io_data_ex_ctrl_aluop;

output io_data_ex_ctrl_branch;
wire io_data_ex_ctrl_branch;

output io_data_ex_ctrl_itype;
wire io_data_ex_ctrl_itype;

output [1:0] io_data_ex_ctrl_jumptype;
wire [1:0] io_data_ex_ctrl_jumptype;

output io_data_ex_ctrl_resultselect;
wire io_data_ex_ctrl_resultselect;

output io_data_ex_ctrl_src1;
wire io_data_ex_ctrl_src1;

output [1:0] io_data_ex_ctrl_src2;
wire [1:0] io_data_ex_ctrl_src2;

output io_data_ex_ctrl_wordinst;
wire io_data_ex_ctrl_wordinst;

output [1:0] io_data_mem_ctrl_memop;
wire [1:0] io_data_mem_ctrl_memop;

output io_data_wb_ctrl_regwrite;
wire io_data_wb_ctrl_regwrite;

output io_data_wb_ctrl_toreg;
wire io_data_wb_ctrl_toreg;

input io_flush;
wire io_flush;

input io_in_ex_ctrl_aluop;
wire io_in_ex_ctrl_aluop;

input io_in_ex_ctrl_branch;
wire io_in_ex_ctrl_branch;

input io_in_ex_ctrl_itype;
wire io_in_ex_ctrl_itype;

input [1:0] io_in_ex_ctrl_jumptype;
wire [1:0] io_in_ex_ctrl_jumptype;

input io_in_ex_ctrl_resultselect;
wire io_in_ex_ctrl_resultselect;

input io_in_ex_ctrl_src1;
wire io_in_ex_ctrl_src1;

input [1:0] io_in_ex_ctrl_src2;
wire [1:0] io_in_ex_ctrl_src2;

input io_in_ex_ctrl_wordinst;
wire io_in_ex_ctrl_wordinst;

input [1:0] io_in_mem_ctrl_memop;
wire [1:0] io_in_mem_ctrl_memop;

input io_in_wb_ctrl_regwrite;
wire io_in_wb_ctrl_regwrite;

input io_in_wb_ctrl_toreg;
wire io_in_wb_ctrl_toreg;

reg reg_ex_ctrl_aluop;

reg reg_ex_ctrl_branch;

reg reg_ex_ctrl_itype;

reg [1:0] reg_ex_ctrl_jumptype;

reg reg_ex_ctrl_resultselect;

reg reg_ex_ctrl_src1;

reg [1:0] reg_ex_ctrl_src2;

reg reg_ex_ctrl_wordinst;

reg [1:0] reg_mem_ctrl_memop;

reg reg_wb_ctrl_regwrite;

reg reg_wb_ctrl_toreg;

input reset;
wire reset;
always @* begin
if (\$auto$verilog_backend.cc:2355:dump_module$466 ) begin end
_10_ = reg_wb_ctrl_toreg;
_09_ = reg_wb_ctrl_regwrite;
_08_ = reg_mem_ctrl_memop;
_02_ = reg_ex_ctrl_itype;
_00_ = reg_ex_ctrl_aluop;
_05_ = reg_ex_ctrl_src1;
_06_ = reg_ex_ctrl_src2;
_01_ = reg_ex_ctrl_branch;
_03_ = reg_ex_ctrl_jumptype;
_04_ = reg_ex_ctrl_resultselect;
_07_ = reg_ex_ctrl_wordinst;

if (reset) begin
_02_ = 1'h0;
end else begin

if (io_flush) begin
_02_ = 1'h0;
end else begin
_02_ = io_in_ex_ctrl_itype;
end
end

if (reset) begin
_00_ = 1'h0;
end else begin

if (io_flush) begin
_00_ = 1'h0;
end else begin
_00_ = io_in_ex_ctrl_aluop;
end
end

if (reset) begin
_05_ = 1'h0;
end else begin

if (io_flush) begin
_05_ = 1'h0;
end else begin
_05_ = io_in_ex_ctrl_src1;
end
end

if (reset) begin
_06_ = 2'h0;
end else begin

if (io_flush) begin
_06_ = 2'h0;
end else begin
_06_ = io_in_ex_ctrl_src2;
end
end

if (reset) begin
_01_ = 1'h0;
end else begin

if (io_flush) begin
_01_ = 1'h0;
end else begin
_01_ = io_in_ex_ctrl_branch;
end
end

if (reset) begin
_03_ = 2'h0;
end else begin

if (io_flush) begin
_03_ = 2'h0;
end else begin
_03_ = io_in_ex_ctrl_jumptype;
end
end

if (reset) begin
_04_ = 1'h0;
end else begin

if (io_flush) begin
_04_ = 1'h0;
end else begin
_04_ = io_in_ex_ctrl_resultselect;
end
end

if (reset) begin
_07_ = 1'h0;
end else begin

if (io_flush) begin
_07_ = 1'h0;
end else begin
_07_ = io_in_ex_ctrl_wordinst;
end
end

if (reset) begin
_08_ = 2'h0;
end else begin

if (io_flush) begin
_08_ = 2'h0;
end else begin
_08_ = io_in_mem_ctrl_memop;
end
end

if (reset) begin
_10_ = 1'h0;
end else begin

if (io_flush) begin
_10_ = 1'h0;
end else begin
_10_ = io_in_wb_ctrl_toreg;
end
end

if (reset) begin
_09_ = 1'h0;
end else begin

if (io_flush) begin
_09_ = 1'h0;
end else begin
_09_ = io_in_wb_ctrl_regwrite;
end
end
end
always @(posedge clock) begin
reg_wb_ctrl_toreg <= _10_;
reg_wb_ctrl_regwrite <= _09_;
reg_mem_ctrl_memop <= _08_;
reg_ex_ctrl_itype <= _02_;
reg_ex_ctrl_aluop <= _00_;
reg_ex_ctrl_src1 <= _05_;
reg_ex_ctrl_src2 <= _06_;
reg_ex_ctrl_branch <= _01_;
reg_ex_ctrl_jumptype <= _03_;
reg_ex_ctrl_resultselect <= _04_;
reg_ex_ctrl_wordinst <= _07_;
end
assign io_data_ex_ctrl_itype = reg_ex_ctrl_itype;
assign io_data_ex_ctrl_aluop = reg_ex_ctrl_aluop;
assign io_data_ex_ctrl_src1 = reg_ex_ctrl_src1;
assign io_data_ex_ctrl_src2 = reg_ex_ctrl_src2;
assign io_data_ex_ctrl_branch = reg_ex_ctrl_branch;
assign io_data_ex_ctrl_jumptype = reg_ex_ctrl_jumptype;
assign io_data_ex_ctrl_resultselect = reg_ex_ctrl_resultselect;
assign io_data_ex_ctrl_wordinst = reg_ex_ctrl_wordinst;
assign io_data_mem_ctrl_memop = reg_mem_ctrl_memop;
assign io_data_wb_ctrl_toreg = reg_wb_ctrl_toreg;
assign io_data_wb_ctrl_regwrite = reg_wb_ctrl_regwrite;
endmodule