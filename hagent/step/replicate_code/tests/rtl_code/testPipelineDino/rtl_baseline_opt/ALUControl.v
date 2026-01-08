





module ALUControl(io_aluop, io_itype, io_funct7, io_funct3, io_wordinst, io_operation);

wire _00_;

wire _01_;

wire _02_;

wire _03_;

wire _04_;

wire _05_;

wire _06_;

wire _07_;

wire _08_;

wire _09_;

wire _10_;

wire _11_;

wire _12_;

wire [4:0] _13_;

wire [4:0] _14_;

wire [4:0] _15_;

wire [4:0] _16_;

wire [4:0] _17_;

wire [4:0] _18_;

wire [4:0] _19_;

wire [4:0] _20_;

wire [4:0] _21_;

wire [2:0] _22_;

wire [4:0] _23_;

wire [4:0] _24_;

wire [4:0] _25_;

wire [4:0] _26_;

wire [4:0] _27_;

wire [4:0] _28_;

wire [4:0] _29_;

wire [4:0] _GEN_0;

wire [4:0] _GEN_1;

wire [4:0] _GEN_10;

wire [4:0] _GEN_11;

wire [4:0] _GEN_12;

wire [4:0] _GEN_13;

wire [4:0] _GEN_14;

wire [4:0] _GEN_15;

wire [4:0] _GEN_2;

wire [4:0] _GEN_3;

wire [4:0] _GEN_4;

wire [4:0] _GEN_5;

wire [4:0] _GEN_6;

wire [4:0] _GEN_7;

wire [4:0] _GEN_8;

wire [2:0] _GEN_9;

wire _T;

wire _T_1;

wire _T_11;

wire _T_13;

wire _T_14;

wire _T_2;

wire _T_3;

wire _T_4;

wire _T_5;

wire _T_6;

wire _T_7;

wire _T_8;

wire _T_9;

input io_aluop;
wire io_aluop;

input [2:0] io_funct3;
wire [2:0] io_funct3;

input [6:0] io_funct7;
wire [6:0] io_funct7;

input io_itype;
wire io_itype;

output [4:0] io_operation;
wire [4:0] io_operation;

input io_wordinst;
wire io_wordinst;
assign _00_ = io_funct3 ==
 3'h0;
assign _01_ = io_funct7 ==
 7'h00;
assign _02_ = io_funct7 ==
 7'h20;
assign _03_ = io_funct3 ==
 3'h1;
assign _04_ = io_funct3 ==
 3'h2;
assign _05_ = io_funct3 ==
 3'h3;
assign _06_ = io_funct3 ==
 3'h4;
assign _07_ = io_funct3 ==
 3'h5;
assign _08_ = io_funct7[6:1] ==
 6'h00;
assign _09_ = io_funct7[6:1] ==
 6'h10;
assign _10_ = io_funct3 ==
 3'h6;
assign _11_ = ~
 io_aluop;
assign _12_ = io_itype |
 _T_2;
assign _13_ = io_wordinst ?
 5'h17 : 5'h07;
assign _14_ = io_wordinst ?
 5'h14 : 5'h04;
assign _15_ = _T_4 ?
 _GEN_1 : 5'h1f;
assign _16_ = _T_3 ?
 _GEN_0 : _GEN_2;
assign _17_ = io_wordinst ?
 5'h18 : 5'h08;
assign _18_ = io_wordinst ?
 5'h12 : 5'h02;
assign _19_ = io_wordinst ?
 5'h13 : 5'h03;
assign _20_ = _T_13 ?
 _GEN_6 : 5'h1f;
assign _21_ = _T_11 ?
 _GEN_5 : _GEN_7;
assign _22_ = _T_14 ?
 3'h5 : 3'h6;
assign _23_ = _T_9 ?
 _GEN_8 : { 2'h0, _GEN_9 };
assign _24_ = _T_8 ?
 5'h00 : _GEN_10;
assign _25_ = _T_7 ?
 5'h01 : _GEN_11;
assign _26_ = _T_6 ?
 5'h09 : _GEN_12;
assign _27_ = _T_5 ?
 _GEN_4 : _GEN_13;
assign _28_ = _T_1 ?
 _GEN_3 : _GEN_14;
assign _29_ = _T ?
 5'h07 : _GEN_15;
assign _T = _11_;
assign _T_1 = _00_;
assign _T_2 = _01_;
assign _T_3 = _12_;
assign _GEN_0 = _13_;
assign _T_4 = _02_;
assign _GEN_1 = _14_;
assign _GEN_2 = _15_;
assign _GEN_3 = _16_;
assign _T_5 = _03_;
assign _GEN_4 = _17_;
assign _T_6 = _04_;
assign _T_7 = _05_;
assign _T_8 = _06_;
assign _T_9 = _07_;
assign _T_11 = _08_;
assign _GEN_5 = _18_;
assign _T_13 = _09_;
assign _GEN_6 = _19_;
assign _GEN_7 = _20_;
assign _GEN_8 = _21_;
assign _T_14 = _10_;
assign _GEN_9 = _22_;
assign _GEN_10 = _23_;
assign _GEN_11 = _24_;
assign _GEN_12 = _25_;
assign _GEN_13 = _26_;
assign _GEN_14 = _27_;
assign _GEN_15 = _28_;
assign io_operation = _29_;
endmodule