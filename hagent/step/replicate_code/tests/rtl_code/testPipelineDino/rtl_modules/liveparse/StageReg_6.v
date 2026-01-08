




































module StageReg_6(clock, reset, io_in_wb_ctrl_toreg, io_in_wb_ctrl_regwrite, io_data_wb_ctrl_toreg, io_data_wb_ctrl_regwrite);
reg \$auto$verilog_backend.cc:2355:dump_module$470 = 0;

reg _0_;

reg _1_;

wire [31:0] _RAND_0;

wire [31:0] _RAND_1;

input clock;
wire clock;

output io_data_wb_ctrl_regwrite;
wire io_data_wb_ctrl_regwrite;

output io_data_wb_ctrl_toreg;
wire io_data_wb_ctrl_toreg;

input io_in_wb_ctrl_regwrite;
wire io_in_wb_ctrl_regwrite;

input io_in_wb_ctrl_toreg;
wire io_in_wb_ctrl_toreg;

reg reg_wb_ctrl_regwrite;

reg reg_wb_ctrl_toreg;

input reset;
wire reset;
always @* begin
if (\$auto$verilog_backend.cc:2355:dump_module$470 ) begin end
_1_ = reg_wb_ctrl_toreg;
_0_ = reg_wb_ctrl_regwrite;

if (reset) begin
_1_ = 1'h0;
end else begin
_1_ = io_in_wb_ctrl_toreg;
end

if (reset) begin
_0_ = 1'h0;
end else begin
_0_ = io_in_wb_ctrl_regwrite;
end
end
always @(posedge clock) begin
reg_wb_ctrl_toreg <= _1_;
reg_wb_ctrl_regwrite <= _0_;
end
assign io_data_wb_ctrl_toreg = reg_wb_ctrl_toreg;
assign io_data_wb_ctrl_regwrite = reg_wb_ctrl_regwrite;
endmodule