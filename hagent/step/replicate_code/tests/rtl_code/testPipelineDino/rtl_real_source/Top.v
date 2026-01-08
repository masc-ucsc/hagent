module Control(
  input  [6:0] io_opcode,
  output       io_itype,
  output       io_aluop,
  output       io_src1,
  output [1:0] io_src2,
  output       io_branch,
  output [1:0] io_jumptype,
  output       io_resultselect,
  output [1:0] io_memop,
  output       io_toreg,
  output       io_regwrite,
  output       io_wordinst
);
  wire  _T_1 = 7'h33 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_3 = 7'h13 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_5 = 7'h3 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_7 = 7'h23 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_9 = 7'h63 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_11 = 7'h37 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_13 = 7'h17 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_15 = 7'h6f == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_17 = 7'h67 == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_19 = 7'h1b == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_21 = 7'h3b == io_opcode; // @[Lookup.scala 31:38]
  wire  _T_24 = _T_17 ? 1'h0 : _T_19; // @[Lookup.scala 33:37]
  wire  _T_25 = _T_15 ? 1'h0 : _T_24; // @[Lookup.scala 33:37]
  wire  _T_26 = _T_13 ? 1'h0 : _T_25; // @[Lookup.scala 33:37]
  wire  _T_27 = _T_11 ? 1'h0 : _T_26; // @[Lookup.scala 33:37]
  wire  _T_28 = _T_9 ? 1'h0 : _T_27; // @[Lookup.scala 33:37]
  wire  _T_29 = _T_7 ? 1'h0 : _T_28; // @[Lookup.scala 33:37]
  wire  _T_30 = _T_5 ? 1'h0 : _T_29; // @[Lookup.scala 33:37]
  wire  _T_31 = _T_3 | _T_30; // @[Lookup.scala 33:37]
  wire  _T_33 = _T_19 | _T_21; // @[Lookup.scala 33:37]
  wire  _T_34 = _T_17 ? 1'h0 : _T_33; // @[Lookup.scala 33:37]
  wire  _T_35 = _T_15 ? 1'h0 : _T_34; // @[Lookup.scala 33:37]
  wire  _T_36 = _T_13 ? 1'h0 : _T_35; // @[Lookup.scala 33:37]
  wire  _T_37 = _T_11 ? 1'h0 : _T_36; // @[Lookup.scala 33:37]
  wire  _T_38 = _T_9 ? 1'h0 : _T_37; // @[Lookup.scala 33:37]
  wire  _T_39 = _T_7 ? 1'h0 : _T_38; // @[Lookup.scala 33:37]
  wire  _T_40 = _T_5 ? 1'h0 : _T_39; // @[Lookup.scala 33:37]
  wire  _T_41 = _T_3 | _T_40; // @[Lookup.scala 33:37]
  wire  _T_45 = _T_15 | _T_17; // @[Lookup.scala 33:37]
  wire  _T_46 = _T_13 | _T_45; // @[Lookup.scala 33:37]
  wire  _T_47 = _T_11 ? 1'h0 : _T_46; // @[Lookup.scala 33:37]
  wire  _T_48 = _T_9 ? 1'h0 : _T_47; // @[Lookup.scala 33:37]
  wire  _T_49 = _T_7 ? 1'h0 : _T_48; // @[Lookup.scala 33:37]
  wire  _T_50 = _T_5 ? 1'h0 : _T_49; // @[Lookup.scala 33:37]
  wire  _T_51 = _T_3 ? 1'h0 : _T_50; // @[Lookup.scala 33:37]
  wire [1:0] _T_54 = _T_17 ? 2'h2 : {{1'd0}, _T_19}; // @[Lookup.scala 33:37]
  wire [1:0] _T_55 = _T_15 ? 2'h2 : _T_54; // @[Lookup.scala 33:37]
  wire [1:0] _T_56 = _T_13 ? 2'h1 : _T_55; // @[Lookup.scala 33:37]
  wire [1:0] _T_57 = _T_11 ? 2'h0 : _T_56; // @[Lookup.scala 33:37]
  wire [1:0] _T_58 = _T_9 ? 2'h0 : _T_57; // @[Lookup.scala 33:37]
  wire [1:0] _T_59 = _T_7 ? 2'h1 : _T_58; // @[Lookup.scala 33:37]
  wire [1:0] _T_60 = _T_5 ? 2'h1 : _T_59; // @[Lookup.scala 33:37]
  wire [1:0] _T_61 = _T_3 ? 2'h1 : _T_60; // @[Lookup.scala 33:37]
  wire  _T_69 = _T_7 ? 1'h0 : _T_9; // @[Lookup.scala 33:37]
  wire  _T_70 = _T_5 ? 1'h0 : _T_69; // @[Lookup.scala 33:37]
  wire  _T_71 = _T_3 ? 1'h0 : _T_70; // @[Lookup.scala 33:37]
  wire [1:0] _T_74 = _T_17 ? 2'h3 : 2'h0; // @[Lookup.scala 33:37]
  wire [1:0] _T_75 = _T_15 ? 2'h2 : _T_74; // @[Lookup.scala 33:37]
  wire [1:0] _T_76 = _T_13 ? 2'h0 : _T_75; // @[Lookup.scala 33:37]
  wire [1:0] _T_77 = _T_11 ? 2'h0 : _T_76; // @[Lookup.scala 33:37]
  wire [1:0] _T_78 = _T_9 ? 2'h0 : _T_77; // @[Lookup.scala 33:37]
  wire [1:0] _T_79 = _T_7 ? 2'h0 : _T_78; // @[Lookup.scala 33:37]
  wire [1:0] _T_80 = _T_5 ? 2'h0 : _T_79; // @[Lookup.scala 33:37]
  wire [1:0] _T_81 = _T_3 ? 2'h0 : _T_80; // @[Lookup.scala 33:37]
  wire  _T_88 = _T_9 ? 1'h0 : _T_11; // @[Lookup.scala 33:37]
  wire  _T_89 = _T_7 ? 1'h0 : _T_88; // @[Lookup.scala 33:37]
  wire  _T_90 = _T_5 ? 1'h0 : _T_89; // @[Lookup.scala 33:37]
  wire  _T_91 = _T_3 ? 1'h0 : _T_90; // @[Lookup.scala 33:37]
  wire [1:0] _T_99 = _T_7 ? 2'h3 : 2'h0; // @[Lookup.scala 33:37]
  wire [1:0] _T_100 = _T_5 ? 2'h2 : _T_99; // @[Lookup.scala 33:37]
  wire [1:0] _T_101 = _T_3 ? 2'h0 : _T_100; // @[Lookup.scala 33:37]
  wire  _T_111 = _T_3 ? 1'h0 : _T_5; // @[Lookup.scala 33:37]
  wire  _T_114 = _T_17 | _T_33; // @[Lookup.scala 33:37]
  wire  _T_115 = _T_15 | _T_114; // @[Lookup.scala 33:37]
  wire  _T_116 = _T_13 | _T_115; // @[Lookup.scala 33:37]
  wire  _T_117 = _T_11 | _T_116; // @[Lookup.scala 33:37]
  wire  _T_118 = _T_9 ? 1'h0 : _T_117; // @[Lookup.scala 33:37]
  wire  _T_119 = _T_7 ? 1'h0 : _T_118; // @[Lookup.scala 33:37]
  wire  _T_120 = _T_5 | _T_119; // @[Lookup.scala 33:37]
  wire  _T_121 = _T_3 | _T_120; // @[Lookup.scala 33:37]
  wire  _T_141 = _T_3 ? 1'h0 : _T_40; // @[Lookup.scala 33:37]
  assign io_itype = _T_1 ? 1'h0 : _T_31; // @[control.scala 78:19]
  assign io_aluop = _T_1 | _T_41; // @[control.scala 79:19]
  assign io_src1 = _T_1 ? 1'h0 : _T_51; // @[control.scala 80:19]
  assign io_src2 = _T_1 ? 2'h0 : _T_61; // @[control.scala 81:19]
  assign io_branch = _T_1 ? 1'h0 : _T_71; // @[control.scala 82:19]
  assign io_jumptype = _T_1 ? 2'h0 : _T_81; // @[control.scala 83:19]
  assign io_resultselect = _T_1 ? 1'h0 : _T_91; // @[control.scala 84:19]
  assign io_memop = _T_1 ? 2'h0 : _T_101; // @[control.scala 85:19]
  assign io_toreg = _T_1 ? 1'h0 : _T_111; // @[control.scala 86:19]
  assign io_regwrite = _T_1 | _T_121; // @[control.scala 87:19]
  assign io_wordinst = _T_1 ? 1'h0 : _T_141; // @[control.scala 89:19]
endmodule
module RegisterFile(
  input         clock,
  input  [4:0]  io_readreg1,
  input  [4:0]  io_readreg2,
  input  [4:0]  io_writereg,
  input  [63:0] io_writedata,
  input         io_wen,
  output [63:0] io_readdata1,
  output [63:0] io_readdata2
);
  reg [63:0] regs_0; // @[register-file.scala 54:17]
  reg [63:0] _RAND_0;
  reg [63:0] regs_1; // @[register-file.scala 54:17]
  reg [63:0] _RAND_1;
  reg [63:0] regs_2; // @[register-file.scala 54:17]
  reg [63:0] _RAND_2;
  reg [63:0] regs_3; // @[register-file.scala 54:17]
  reg [63:0] _RAND_3;
  reg [63:0] regs_4; // @[register-file.scala 54:17]
  reg [63:0] _RAND_4;
  reg [63:0] regs_5; // @[register-file.scala 54:17]
  reg [63:0] _RAND_5;
  reg [63:0] regs_6; // @[register-file.scala 54:17]
  reg [63:0] _RAND_6;
  reg [63:0] regs_7; // @[register-file.scala 54:17]
  reg [63:0] _RAND_7;
  reg [63:0] regs_8; // @[register-file.scala 54:17]
  reg [63:0] _RAND_8;
  reg [63:0] regs_9; // @[register-file.scala 54:17]
  reg [63:0] _RAND_9;
  reg [63:0] regs_10; // @[register-file.scala 54:17]
  reg [63:0] _RAND_10;
  reg [63:0] regs_11; // @[register-file.scala 54:17]
  reg [63:0] _RAND_11;
  reg [63:0] regs_12; // @[register-file.scala 54:17]
  reg [63:0] _RAND_12;
  reg [63:0] regs_13; // @[register-file.scala 54:17]
  reg [63:0] _RAND_13;
  reg [63:0] regs_14; // @[register-file.scala 54:17]
  reg [63:0] _RAND_14;
  reg [63:0] regs_15; // @[register-file.scala 54:17]
  reg [63:0] _RAND_15;
  reg [63:0] regs_16; // @[register-file.scala 54:17]
  reg [63:0] _RAND_16;
  reg [63:0] regs_17; // @[register-file.scala 54:17]
  reg [63:0] _RAND_17;
  reg [63:0] regs_18; // @[register-file.scala 54:17]
  reg [63:0] _RAND_18;
  reg [63:0] regs_19; // @[register-file.scala 54:17]
  reg [63:0] _RAND_19;
  reg [63:0] regs_20; // @[register-file.scala 54:17]
  reg [63:0] _RAND_20;
  reg [63:0] regs_21; // @[register-file.scala 54:17]
  reg [63:0] _RAND_21;
  reg [63:0] regs_22; // @[register-file.scala 54:17]
  reg [63:0] _RAND_22;
  reg [63:0] regs_23; // @[register-file.scala 54:17]
  reg [63:0] _RAND_23;
  reg [63:0] regs_24; // @[register-file.scala 54:17]
  reg [63:0] _RAND_24;
  reg [63:0] regs_25; // @[register-file.scala 54:17]
  reg [63:0] _RAND_25;
  reg [63:0] regs_26; // @[register-file.scala 54:17]
  reg [63:0] _RAND_26;
  reg [63:0] regs_27; // @[register-file.scala 54:17]
  reg [63:0] _RAND_27;
  reg [63:0] regs_28; // @[register-file.scala 54:17]
  reg [63:0] _RAND_28;
  reg [63:0] regs_29; // @[register-file.scala 54:17]
  reg [63:0] _RAND_29;
  reg [63:0] regs_30; // @[register-file.scala 54:17]
  reg [63:0] _RAND_30;
  reg [63:0] regs_31; // @[register-file.scala 54:17]
  reg [63:0] _RAND_31;
  wire [63:0] _GEN_65 = 5'h1 == io_readreg1 ? regs_1 : regs_0; // @[register-file.scala 63:16]
  wire [63:0] _GEN_66 = 5'h2 == io_readreg1 ? regs_2 : _GEN_65; // @[register-file.scala 63:16]
  wire [63:0] _GEN_67 = 5'h3 == io_readreg1 ? regs_3 : _GEN_66; // @[register-file.scala 63:16]
  wire [63:0] _GEN_68 = 5'h4 == io_readreg1 ? regs_4 : _GEN_67; // @[register-file.scala 63:16]
  wire [63:0] _GEN_69 = 5'h5 == io_readreg1 ? regs_5 : _GEN_68; // @[register-file.scala 63:16]
  wire [63:0] _GEN_70 = 5'h6 == io_readreg1 ? regs_6 : _GEN_69; // @[register-file.scala 63:16]
  wire [63:0] _GEN_71 = 5'h7 == io_readreg1 ? regs_7 : _GEN_70; // @[register-file.scala 63:16]
  wire [63:0] _GEN_72 = 5'h8 == io_readreg1 ? regs_8 : _GEN_71; // @[register-file.scala 63:16]
  wire [63:0] _GEN_73 = 5'h9 == io_readreg1 ? regs_9 : _GEN_72; // @[register-file.scala 63:16]
  wire [63:0] _GEN_74 = 5'ha == io_readreg1 ? regs_10 : _GEN_73; // @[register-file.scala 63:16]
  wire [63:0] _GEN_75 = 5'hb == io_readreg1 ? regs_11 : _GEN_74; // @[register-file.scala 63:16]
  wire [63:0] _GEN_76 = 5'hc == io_readreg1 ? regs_12 : _GEN_75; // @[register-file.scala 63:16]
  wire [63:0] _GEN_77 = 5'hd == io_readreg1 ? regs_13 : _GEN_76; // @[register-file.scala 63:16]
  wire [63:0] _GEN_78 = 5'he == io_readreg1 ? regs_14 : _GEN_77; // @[register-file.scala 63:16]
  wire [63:0] _GEN_79 = 5'hf == io_readreg1 ? regs_15 : _GEN_78; // @[register-file.scala 63:16]
  wire [63:0] _GEN_80 = 5'h10 == io_readreg1 ? regs_16 : _GEN_79; // @[register-file.scala 63:16]
  wire [63:0] _GEN_81 = 5'h11 == io_readreg1 ? regs_17 : _GEN_80; // @[register-file.scala 63:16]
  wire [63:0] _GEN_82 = 5'h12 == io_readreg1 ? regs_18 : _GEN_81; // @[register-file.scala 63:16]
  wire [63:0] _GEN_83 = 5'h13 == io_readreg1 ? regs_19 : _GEN_82; // @[register-file.scala 63:16]
  wire [63:0] _GEN_84 = 5'h14 == io_readreg1 ? regs_20 : _GEN_83; // @[register-file.scala 63:16]
  wire [63:0] _GEN_85 = 5'h15 == io_readreg1 ? regs_21 : _GEN_84; // @[register-file.scala 63:16]
  wire [63:0] _GEN_86 = 5'h16 == io_readreg1 ? regs_22 : _GEN_85; // @[register-file.scala 63:16]
  wire [63:0] _GEN_87 = 5'h17 == io_readreg1 ? regs_23 : _GEN_86; // @[register-file.scala 63:16]
  wire [63:0] _GEN_88 = 5'h18 == io_readreg1 ? regs_24 : _GEN_87; // @[register-file.scala 63:16]
  wire [63:0] _GEN_89 = 5'h19 == io_readreg1 ? regs_25 : _GEN_88; // @[register-file.scala 63:16]
  wire [63:0] _GEN_90 = 5'h1a == io_readreg1 ? regs_26 : _GEN_89; // @[register-file.scala 63:16]
  wire [63:0] _GEN_91 = 5'h1b == io_readreg1 ? regs_27 : _GEN_90; // @[register-file.scala 63:16]
  wire [63:0] _GEN_92 = 5'h1c == io_readreg1 ? regs_28 : _GEN_91; // @[register-file.scala 63:16]
  wire [63:0] _GEN_93 = 5'h1d == io_readreg1 ? regs_29 : _GEN_92; // @[register-file.scala 63:16]
  wire [63:0] _GEN_94 = 5'h1e == io_readreg1 ? regs_30 : _GEN_93; // @[register-file.scala 63:16]
  wire [63:0] _GEN_95 = 5'h1f == io_readreg1 ? regs_31 : _GEN_94; // @[register-file.scala 63:16]
  wire [63:0] _GEN_97 = 5'h1 == io_readreg2 ? regs_1 : regs_0; // @[register-file.scala 65:16]
  wire [63:0] _GEN_98 = 5'h2 == io_readreg2 ? regs_2 : _GEN_97; // @[register-file.scala 65:16]
  wire [63:0] _GEN_99 = 5'h3 == io_readreg2 ? regs_3 : _GEN_98; // @[register-file.scala 65:16]
  wire [63:0] _GEN_100 = 5'h4 == io_readreg2 ? regs_4 : _GEN_99; // @[register-file.scala 65:16]
  wire [63:0] _GEN_101 = 5'h5 == io_readreg2 ? regs_5 : _GEN_100; // @[register-file.scala 65:16]
  wire [63:0] _GEN_102 = 5'h6 == io_readreg2 ? regs_6 : _GEN_101; // @[register-file.scala 65:16]
  wire [63:0] _GEN_103 = 5'h7 == io_readreg2 ? regs_7 : _GEN_102; // @[register-file.scala 65:16]
  wire [63:0] _GEN_104 = 5'h8 == io_readreg2 ? regs_8 : _GEN_103; // @[register-file.scala 65:16]
  wire [63:0] _GEN_105 = 5'h9 == io_readreg2 ? regs_9 : _GEN_104; // @[register-file.scala 65:16]
  wire [63:0] _GEN_106 = 5'ha == io_readreg2 ? regs_10 : _GEN_105; // @[register-file.scala 65:16]
  wire [63:0] _GEN_107 = 5'hb == io_readreg2 ? regs_11 : _GEN_106; // @[register-file.scala 65:16]
  wire [63:0] _GEN_108 = 5'hc == io_readreg2 ? regs_12 : _GEN_107; // @[register-file.scala 65:16]
  wire [63:0] _GEN_109 = 5'hd == io_readreg2 ? regs_13 : _GEN_108; // @[register-file.scala 65:16]
  wire [63:0] _GEN_110 = 5'he == io_readreg2 ? regs_14 : _GEN_109; // @[register-file.scala 65:16]
  wire [63:0] _GEN_111 = 5'hf == io_readreg2 ? regs_15 : _GEN_110; // @[register-file.scala 65:16]
  wire [63:0] _GEN_112 = 5'h10 == io_readreg2 ? regs_16 : _GEN_111; // @[register-file.scala 65:16]
  wire [63:0] _GEN_113 = 5'h11 == io_readreg2 ? regs_17 : _GEN_112; // @[register-file.scala 65:16]
  wire [63:0] _GEN_114 = 5'h12 == io_readreg2 ? regs_18 : _GEN_113; // @[register-file.scala 65:16]
  wire [63:0] _GEN_115 = 5'h13 == io_readreg2 ? regs_19 : _GEN_114; // @[register-file.scala 65:16]
  wire [63:0] _GEN_116 = 5'h14 == io_readreg2 ? regs_20 : _GEN_115; // @[register-file.scala 65:16]
  wire [63:0] _GEN_117 = 5'h15 == io_readreg2 ? regs_21 : _GEN_116; // @[register-file.scala 65:16]
  wire [63:0] _GEN_118 = 5'h16 == io_readreg2 ? regs_22 : _GEN_117; // @[register-file.scala 65:16]
  wire [63:0] _GEN_119 = 5'h17 == io_readreg2 ? regs_23 : _GEN_118; // @[register-file.scala 65:16]
  wire [63:0] _GEN_120 = 5'h18 == io_readreg2 ? regs_24 : _GEN_119; // @[register-file.scala 65:16]
  wire [63:0] _GEN_121 = 5'h19 == io_readreg2 ? regs_25 : _GEN_120; // @[register-file.scala 65:16]
  wire [63:0] _GEN_122 = 5'h1a == io_readreg2 ? regs_26 : _GEN_121; // @[register-file.scala 65:16]
  wire [63:0] _GEN_123 = 5'h1b == io_readreg2 ? regs_27 : _GEN_122; // @[register-file.scala 65:16]
  wire [63:0] _GEN_124 = 5'h1c == io_readreg2 ? regs_28 : _GEN_123; // @[register-file.scala 65:16]
  wire [63:0] _GEN_125 = 5'h1d == io_readreg2 ? regs_29 : _GEN_124; // @[register-file.scala 65:16]
  wire [63:0] _GEN_126 = 5'h1e == io_readreg2 ? regs_30 : _GEN_125; // @[register-file.scala 65:16]
  wire [63:0] _GEN_127 = 5'h1f == io_readreg2 ? regs_31 : _GEN_126; // @[register-file.scala 65:16]
  wire  _T = io_readreg1 == io_writereg; // @[register-file.scala 66:30]
  wire  potato3 = _T & io_wen; // @[register-file.scala 66:46]
  wire  _T_1 = io_readreg2 == io_writereg; // @[register-file.scala 73:23]
  wire  _T_2 = _T_1 & io_wen; // @[register-file.scala 73:39]
  assign io_readdata1 = potato3 ? io_writedata : _GEN_95; // @[register-file.scala 63:16 register-file.scala 71:20]
  assign io_readdata2 = _T_2 ? io_writedata : _GEN_127; // @[register-file.scala 65:16 register-file.scala 74:20]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {2{`RANDOM}};
  regs_0 = _RAND_0[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {2{`RANDOM}};
  regs_1 = _RAND_1[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {2{`RANDOM}};
  regs_2 = _RAND_2[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {2{`RANDOM}};
  regs_3 = _RAND_3[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {2{`RANDOM}};
  regs_4 = _RAND_4[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {2{`RANDOM}};
  regs_5 = _RAND_5[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_6 = {2{`RANDOM}};
  regs_6 = _RAND_6[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_7 = {2{`RANDOM}};
  regs_7 = _RAND_7[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_8 = {2{`RANDOM}};
  regs_8 = _RAND_8[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_9 = {2{`RANDOM}};
  regs_9 = _RAND_9[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_10 = {2{`RANDOM}};
  regs_10 = _RAND_10[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_11 = {2{`RANDOM}};
  regs_11 = _RAND_11[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_12 = {2{`RANDOM}};
  regs_12 = _RAND_12[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_13 = {2{`RANDOM}};
  regs_13 = _RAND_13[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_14 = {2{`RANDOM}};
  regs_14 = _RAND_14[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_15 = {2{`RANDOM}};
  regs_15 = _RAND_15[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_16 = {2{`RANDOM}};
  regs_16 = _RAND_16[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_17 = {2{`RANDOM}};
  regs_17 = _RAND_17[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_18 = {2{`RANDOM}};
  regs_18 = _RAND_18[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_19 = {2{`RANDOM}};
  regs_19 = _RAND_19[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_20 = {2{`RANDOM}};
  regs_20 = _RAND_20[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_21 = {2{`RANDOM}};
  regs_21 = _RAND_21[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_22 = {2{`RANDOM}};
  regs_22 = _RAND_22[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_23 = {2{`RANDOM}};
  regs_23 = _RAND_23[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_24 = {2{`RANDOM}};
  regs_24 = _RAND_24[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_25 = {2{`RANDOM}};
  regs_25 = _RAND_25[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_26 = {2{`RANDOM}};
  regs_26 = _RAND_26[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_27 = {2{`RANDOM}};
  regs_27 = _RAND_27[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_28 = {2{`RANDOM}};
  regs_28 = _RAND_28[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_29 = {2{`RANDOM}};
  regs_29 = _RAND_29[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_30 = {2{`RANDOM}};
  regs_30 = _RAND_30[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_31 = {2{`RANDOM}};
  regs_31 = _RAND_31[63:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (io_wen) begin
      if (5'h0 == io_writereg) begin
        regs_0 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h1 == io_writereg) begin
        regs_1 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h2 == io_writereg) begin
        regs_2 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h3 == io_writereg) begin
        regs_3 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h4 == io_writereg) begin
        regs_4 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h5 == io_writereg) begin
        regs_5 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h6 == io_writereg) begin
        regs_6 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h7 == io_writereg) begin
        regs_7 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h8 == io_writereg) begin
        regs_8 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h9 == io_writereg) begin
        regs_9 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'ha == io_writereg) begin
        regs_10 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'hb == io_writereg) begin
        regs_11 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'hc == io_writereg) begin
        regs_12 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'hd == io_writereg) begin
        regs_13 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'he == io_writereg) begin
        regs_14 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'hf == io_writereg) begin
        regs_15 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h10 == io_writereg) begin
        regs_16 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h11 == io_writereg) begin
        regs_17 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h12 == io_writereg) begin
        regs_18 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h13 == io_writereg) begin
        regs_19 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h14 == io_writereg) begin
        regs_20 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h15 == io_writereg) begin
        regs_21 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h16 == io_writereg) begin
        regs_22 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h17 == io_writereg) begin
        regs_23 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h18 == io_writereg) begin
        regs_24 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h19 == io_writereg) begin
        regs_25 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h1a == io_writereg) begin
        regs_26 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h1b == io_writereg) begin
        regs_27 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h1c == io_writereg) begin
        regs_28 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h1d == io_writereg) begin
        regs_29 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h1e == io_writereg) begin
        regs_30 <= io_writedata;
      end
    end
    if (io_wen) begin
      if (5'h1f == io_writereg) begin
        regs_31 <= io_writedata;
      end
    end
  end
endmodule
module ALUControl(
  input        io_aluop,
  input        io_itype,
  input  [6:0] io_funct7,
  input  [2:0] io_funct3,
  input        io_wordinst,
  output [4:0] io_operation
);
  wire  _T = ~io_aluop; // @[alucontrol.scala 33:18]
  wire  _T_1 = io_funct3 == 3'h0; // @[alucontrol.scala 36:21]
  wire  _T_2 = io_funct7 == 7'h0; // @[alucontrol.scala 37:34]
  wire  _T_3 = io_itype | _T_2; // @[alucontrol.scala 37:22]
  wire [4:0] _GEN_0 = io_wordinst ? 5'h17 : 5'h7; // @[alucontrol.scala 38:28]
  wire  _T_4 = io_funct7 == 7'h20; // @[alucontrol.scala 43:30]
  wire [4:0] _GEN_1 = io_wordinst ? 5'h14 : 5'h4; // @[alucontrol.scala 44:36]
  wire [4:0] _GEN_2 = _T_4 ? _GEN_1 : 5'h1f; // @[alucontrol.scala 43:48]
  wire [4:0] _GEN_3 = _T_3 ? _GEN_0 : _GEN_2; // @[alucontrol.scala 37:52]
  wire  _T_5 = io_funct3 == 3'h1; // @[alucontrol.scala 52:28]
  wire [4:0] _GEN_4 = io_wordinst ? 5'h18 : 5'h8; // @[alucontrol.scala 53:26]
  wire  _T_6 = io_funct3 == 3'h2; // @[alucontrol.scala 58:28]
  wire  _T_7 = io_funct3 == 3'h3; // @[alucontrol.scala 60:28]
  wire  _T_8 = io_funct3 == 3'h4; // @[alucontrol.scala 62:28]
  wire  _T_9 = io_funct3 == 3'h5; // @[alucontrol.scala 64:28]
  wire  _T_11 = io_funct7[6:1] == 6'h0; // @[alucontrol.scala 65:28]
  wire [4:0] _GEN_5 = io_wordinst ? 5'h12 : 5'h2; // @[alucontrol.scala 66:28]
  wire  _T_13 = io_funct7[6:1] == 6'h10; // @[alucontrol.scala 71:35]
  wire [4:0] _GEN_6 = io_wordinst ? 5'h13 : 5'h3; // @[alucontrol.scala 72:28]
  wire [4:0] _GEN_7 = _T_13 ? _GEN_6 : 5'h1f; // @[alucontrol.scala 71:52]
  wire [4:0] _GEN_8 = _T_11 ? _GEN_5 : _GEN_7; // @[alucontrol.scala 65:45]
  wire  _T_14 = io_funct3 == 3'h6; // @[alucontrol.scala 80:28]
  wire [2:0] _GEN_9 = _T_14 ? 3'h5 : 3'h6; // @[alucontrol.scala 80:42]
  wire [4:0] _GEN_10 = _T_9 ? _GEN_8 : {{2'd0}, _GEN_9}; // @[alucontrol.scala 64:42]
  wire [4:0] _GEN_11 = _T_8 ? 5'h0 : _GEN_10; // @[alucontrol.scala 62:42]
  wire [4:0] _GEN_12 = _T_7 ? 5'h1 : _GEN_11; // @[alucontrol.scala 60:42]
  wire [4:0] _GEN_13 = _T_6 ? 5'h9 : _GEN_12; // @[alucontrol.scala 58:42]
  wire [4:0] _GEN_14 = _T_5 ? _GEN_4 : _GEN_13; // @[alucontrol.scala 52:42]
  wire [4:0] _GEN_15 = _T_1 ? _GEN_3 : _GEN_14; // @[alucontrol.scala 36:35]
  assign io_operation = _T ? 5'h7 : _GEN_15; // @[alucontrol.scala 34:18 alucontrol.scala 39:24 alucontrol.scala 41:24 alucontrol.scala 45:24 alucontrol.scala 47:24 alucontrol.scala 50:22 alucontrol.scala 54:22 alucontrol.scala 56:22 alucontrol.scala 59:20 alucontrol.scala 61:20 alucontrol.scala 63:20 alucontrol.scala 67:24 alucontrol.scala 69:24 alucontrol.scala 73:24 alucontrol.scala 75:24 alucontrol.scala 78:22 alucontrol.scala 81:20 alucontrol.scala 83:20]
endmodule
module ALU(
  input  [4:0]  io_operation,
  input  [63:0] io_inputx,
  input  [63:0] io_inputy,
  output [63:0] io_result
);
  wire  wordinst = io_operation[4]; // @[alu.scala 26:34]
  wire [3:0] aluop = io_operation[3:0]; // @[alu.scala 27:27]
  wire [31:0] operand1_32 = io_inputx[31:0]; // @[alu.scala 31:30]
  wire [31:0] operand2_32 = io_inputy[31:0]; // @[alu.scala 32:30]
  wire [126:0] _GEN_20 = {{63'd0}, io_inputx}; // @[alu.scala 33:27]
  wire [126:0] potato2 = _GEN_20 << io_inputy[5:0]; // @[alu.scala 33:27]
  wire [63:0] potato4 = io_inputx | io_inputy; // @[alu.scala 35:27]
  wire  _T_3 = aluop == 4'h6; // @[alu.scala 37:15]
  wire [63:0] _T_4 = io_inputx & io_inputy; // @[alu.scala 38:28]
  wire  _T_5 = aluop == 4'h5; // @[alu.scala 40:20]
  wire  _T_6 = aluop == 4'h7; // @[alu.scala 43:20]
  wire [31:0] _T_9 = operand1_32 + operand2_32; // @[alu.scala 45:49]
  wire [31:0] _T_12 = _T_9[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_14 = {_T_12,_T_9}; // @[Cat.scala 30:58]
  wire [63:0] _T_16 = io_inputx + io_inputy; // @[alu.scala 47:30]
  wire [63:0] _GEN_0 = wordinst ? _T_14 : _T_16; // @[alu.scala 44:32]
  wire  _T_17 = aluop == 4'h4; // @[alu.scala 50:20]
  wire [31:0] _T_20 = operand1_32 - operand2_32; // @[alu.scala 52:49]
  wire [31:0] _T_23 = _T_20[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_25 = {_T_23,_T_20}; // @[Cat.scala 30:58]
  wire [63:0] _T_27 = io_inputx - io_inputy; // @[alu.scala 54:30]
  wire [63:0] _GEN_1 = wordinst ? _T_25 : _T_27; // @[alu.scala 51:32]
  wire  _T_28 = aluop == 4'h3; // @[alu.scala 57:20]
  wire [31:0] _T_30 = io_inputx[31:0]; // @[alu.scala 59:50]
  wire [31:0] _T_33 = $signed(_T_30) >>> operand2_32[4:0]; // @[alu.scala 59:79]
  wire [31:0] _T_36 = _T_33[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_38 = {_T_36,_T_33}; // @[Cat.scala 30:58]
  wire [63:0] _T_42 = $signed(io_inputx) >>> io_inputy[5:0]; // @[alu.scala 62:58]
  wire [63:0] _GEN_2 = wordinst ? _T_38 : _T_42; // @[alu.scala 58:32]
  wire  _T_43 = aluop == 4'h1; // @[alu.scala 65:20]
  wire  _T_44 = io_inputx < io_inputy; // @[alu.scala 66:29]
  wire  _T_45 = aluop == 4'h0; // @[alu.scala 68:20]
  wire [63:0] _T_46 = io_inputx ^ io_inputy; // @[alu.scala 69:28]
  wire  _T_47 = aluop == 4'h2; // @[alu.scala 71:20]
  wire [31:0] _T_50 = operand1_32 >> operand2_32[4:0]; // @[alu.scala 73:49]
  wire [31:0] _T_53 = _T_50[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_55 = {_T_53,_T_50}; // @[Cat.scala 30:58]
  wire [63:0] _T_57 = io_inputx >> io_inputy[5:0]; // @[alu.scala 75:30]
  wire [63:0] _GEN_3 = wordinst ? _T_55 : _T_57; // @[alu.scala 72:32]
  wire  _T_58 = aluop == 4'h9; // @[alu.scala 78:20]
  wire  _T_61 = $signed(io_inputx) < $signed(io_inputy); // @[alu.scala 79:36]
  wire  _T_62 = aluop == 4'h8; // @[alu.scala 81:20]
  wire [62:0] _GEN_21 = {{31'd0}, operand1_32}; // @[alu.scala 83:49]
  wire [62:0] _T_65 = _GEN_21 << operand2_32[4:0]; // @[alu.scala 83:49]
  wire [31:0] _T_68 = _T_65[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_70 = {_T_68,_T_65[31:0]}; // @[Cat.scala 30:58]
  wire [126:0] _GEN_4 = wordinst ? {{63'd0}, _T_70} : potato2; // @[alu.scala 82:32]
  wire  _T_71 = aluop == 4'ha; // @[alu.scala 88:20]
  wire [63:0] _T_73 = ~potato4; // @[alu.scala 89:18]
  wire  _T_74 = aluop == 4'hb; // @[alu.scala 91:20]
  wire  _T_77 = $signed(io_inputx) >= $signed(io_inputy); // @[alu.scala 92:36]
  wire  _T_78 = aluop == 4'hc; // @[alu.scala 94:20]
  wire  _T_79 = io_inputx >= io_inputy; // @[alu.scala 95:29]
  wire  _T_80 = aluop == 4'hd; // @[alu.scala 97:20]
  wire  _T_81 = io_inputx == io_inputy; // @[alu.scala 98:28]
  wire  _T_82 = aluop == 4'he; // @[alu.scala 100:20]
  wire  _T_83 = io_inputx != io_inputy; // @[alu.scala 101:28]
  wire  _GEN_5 = _T_82 & _T_83; // @[alu.scala 100:35]
  wire  _GEN_6 = _T_80 ? _T_81 : _GEN_5; // @[alu.scala 97:35]
  wire  _GEN_7 = _T_78 ? _T_79 : _GEN_6; // @[alu.scala 94:35]
  wire  _GEN_8 = _T_74 ? _T_77 : _GEN_7; // @[alu.scala 91:35]
  wire [63:0] _GEN_9 = _T_71 ? _T_73 : {{63'd0}, _GEN_8}; // @[alu.scala 88:35]
  wire [126:0] _GEN_10 = _T_62 ? _GEN_4 : {{63'd0}, _GEN_9}; // @[alu.scala 81:35]
  wire [126:0] _GEN_11 = _T_58 ? {{126'd0}, _T_61} : _GEN_10; // @[alu.scala 78:35]
  wire [126:0] _GEN_12 = _T_47 ? {{63'd0}, _GEN_3} : _GEN_11; // @[alu.scala 71:35]
  wire [126:0] _GEN_13 = _T_45 ? {{63'd0}, _T_46} : _GEN_12; // @[alu.scala 68:35]
  wire [126:0] _GEN_14 = _T_43 ? {{126'd0}, _T_44} : _GEN_13; // @[alu.scala 65:35]
  wire [126:0] _GEN_15 = _T_28 ? {{63'd0}, _GEN_2} : _GEN_14; // @[alu.scala 57:35]
  wire [126:0] _GEN_16 = _T_17 ? {{63'd0}, _GEN_1} : _GEN_15; // @[alu.scala 50:35]
  wire [126:0] _GEN_17 = _T_6 ? {{63'd0}, _GEN_0} : _GEN_16; // @[alu.scala 43:35]
  wire [126:0] _GEN_18 = _T_5 ? {{63'd0}, potato4} : _GEN_17; // @[alu.scala 40:35]
  wire [126:0] _GEN_19 = _T_3 ? {{63'd0}, _T_4} : _GEN_18; // @[alu.scala 37:30]
  assign io_result = _GEN_19[63:0]; // @[alu.scala 38:15 alu.scala 41:15 alu.scala 45:17 alu.scala 47:17 alu.scala 52:17 alu.scala 54:17 alu.scala 59:17 alu.scala 62:17 alu.scala 66:15 alu.scala 69:15 alu.scala 73:17 alu.scala 75:17 alu.scala 79:15 alu.scala 83:17 alu.scala 85:17 alu.scala 89:15 alu.scala 92:15 alu.scala 95:15 alu.scala 98:15 alu.scala 101:15 alu.scala 104:15]
endmodule
module ImmediateGenerator(
  input  [63:0] io_instruction,
  output [63:0] io_sextImm
);
  wire [6:0] opcode = io_instruction[6:0]; // @[helpers.scala 45:30]
  wire  _T = 7'h37 == opcode; // @[Conditional.scala 37:30]
  wire [31:0] _T_4 = io_instruction[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_7 = {_T_4,io_instruction[31:12],12'h0}; // @[Cat.scala 30:58]
  wire  _T_8 = 7'h17 == opcode; // @[Conditional.scala 37:30]
  wire  _T_16 = 7'h6f == opcode; // @[Conditional.scala 37:30]
  wire [19:0] _T_23 = {io_instruction[31],io_instruction[19:12],io_instruction[20],io_instruction[30:21]}; // @[Cat.scala 30:58]
  wire [42:0] _T_26 = _T_23[19] ? 43'h7ffffffffff : 43'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_28 = {_T_26,io_instruction[31],io_instruction[19:12],io_instruction[20],io_instruction[30:21],1'h0}; // @[Cat.scala 30:58]
  wire  _T_29 = 7'h67 == opcode; // @[Conditional.scala 37:30]
  wire [51:0] _T_33 = io_instruction[31] ? 52'hfffffffffffff : 52'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_34 = {_T_33,io_instruction[31:20]}; // @[Cat.scala 30:58]
  wire  _T_35 = 7'h63 == opcode; // @[Conditional.scala 37:30]
  wire [11:0] _T_42 = {io_instruction[31],io_instruction[7],io_instruction[30:25],io_instruction[11:8]}; // @[Cat.scala 30:58]
  wire [50:0] _T_45 = _T_42[11] ? 51'h7ffffffffffff : 51'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_47 = {_T_45,io_instruction[31],io_instruction[7],io_instruction[30:25],io_instruction[11:8],1'h0}; // @[Cat.scala 30:58]
  wire  _T_48 = 7'h3 == opcode; // @[Conditional.scala 37:30]
  wire  _T_54 = 7'h23 == opcode; // @[Conditional.scala 37:30]
  wire [11:0] _T_57 = {io_instruction[31:25],io_instruction[11:7]}; // @[Cat.scala 30:58]
  wire [51:0] _T_60 = _T_57[11] ? 52'hfffffffffffff : 52'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_61 = {_T_60,io_instruction[31:25],io_instruction[11:7]}; // @[Cat.scala 30:58]
  wire  _T_62 = 7'h13 == opcode; // @[Conditional.scala 37:30]
  wire  _T_68 = 7'h1b == opcode; // @[Conditional.scala 37:30]
  wire  _T_74 = 7'h73 == opcode; // @[Conditional.scala 37:30]
  wire [63:0] _T_77 = {59'h0,io_instruction[19:15]}; // @[Cat.scala 30:58]
  wire [63:0] _GEN_0 = _T_74 ? _T_77 : 64'h0; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_1 = _T_68 ? _T_34 : _GEN_0; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_2 = _T_62 ? _T_34 : _GEN_1; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_3 = _T_54 ? _T_61 : _GEN_2; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_4 = _T_48 ? _T_34 : _GEN_3; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_5 = _T_35 ? _T_47 : _GEN_4; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_6 = _T_29 ? _T_34 : _GEN_5; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_7 = _T_16 ? _T_28 : _GEN_6; // @[Conditional.scala 39:67]
  wire [63:0] _GEN_8 = _T_8 ? _T_7 : _GEN_7; // @[Conditional.scala 39:67]
  assign io_sextImm = _T ? _T_7 : _GEN_8; // @[helpers.scala 43:14 helpers.scala 53:18 helpers.scala 60:18 helpers.scala 67:18 helpers.scala 71:18 helpers.scala 76:18 helpers.scala 80:18 helpers.scala 84:18 helpers.scala 88:18 helpers.scala 92:18 helpers.scala 95:18]
endmodule
module NextPC(
  input         io_branch,
  input  [1:0]  io_jumptype,
  input  [63:0] io_inputx,
  input  [63:0] io_inputy,
  input  [2:0]  io_funct3,
  input  [63:0] io_pc,
  input  [63:0] io_imm,
  output [63:0] io_nextpc,
  output        io_taken
);
  wire  potato6 = io_jumptype != 2'h0; // @[nextpc.scala 36:29]
  wire  _T = io_funct3 == 3'h7; // @[nextpc.scala 38:27]
  wire  _T_1 = io_inputx >= io_inputy; // @[nextpc.scala 38:52]
  wire  potato7 = _T & _T_1; // @[nextpc.scala 38:40]
  wire  _T_2 = io_funct3 == 3'h0; // @[nextpc.scala 41:23]
  wire  _T_3 = io_inputx == io_inputy; // @[nextpc.scala 41:48]
  wire  _T_4 = _T_2 & _T_3; // @[nextpc.scala 41:36]
  wire  _T_5 = io_funct3 == 3'h1; // @[nextpc.scala 42:23]
  wire  _T_6 = io_inputx != io_inputy; // @[nextpc.scala 42:48]
  wire  _T_7 = _T_5 & _T_6; // @[nextpc.scala 42:36]
  wire  _T_8 = _T_4 | _T_7; // @[nextpc.scala 42:10]
  wire  _T_9 = io_funct3 == 3'h4; // @[nextpc.scala 43:23]
  wire  _T_12 = $signed(io_inputx) < $signed(io_inputy); // @[nextpc.scala 43:55]
  wire  _T_13 = _T_9 & _T_12; // @[nextpc.scala 43:36]
  wire  _T_14 = _T_8 | _T_13; // @[nextpc.scala 43:10]
  wire  _T_15 = io_funct3 == 3'h5; // @[nextpc.scala 44:23]
  wire  _T_18 = $signed(io_inputx) >= $signed(io_inputy); // @[nextpc.scala 44:55]
  wire  _T_19 = _T_15 & _T_18; // @[nextpc.scala 44:36]
  wire  _T_20 = _T_14 | _T_19; // @[nextpc.scala 44:10]
  wire  _T_21 = io_funct3 == 3'h6; // @[nextpc.scala 45:23]
  wire  _T_22 = io_inputx < io_inputy; // @[nextpc.scala 45:48]
  wire  _T_23 = _T_21 & _T_22; // @[nextpc.scala 45:36]
  wire  _T_24 = _T_20 | _T_23; // @[nextpc.scala 45:10]
  wire  _T_25 = _T_24 | potato7; // @[nextpc.scala 46:10]
  wire [63:0] _T_27 = io_pc + io_imm; // @[nextpc.scala 47:26]
  wire [63:0] _T_29 = io_pc + 64'h4; // @[nextpc.scala 51:26]
  wire [63:0] _GEN_0 = _T_25 ? _T_27 : _T_29; // @[nextpc.scala 46:23]
  wire [63:0] _T_32 = io_inputx + io_imm; // @[nextpc.scala 55:48]
  wire [63:0] _T_35 = io_jumptype[0] ? _T_32 : _T_27; // @[nextpc.scala 55:21]
  wire [63:0] _GEN_2 = potato6 ? _T_35 : _T_29; // @[nextpc.scala 54:25]
  assign io_nextpc = io_branch ? _GEN_0 : _GEN_2; // @[nextpc.scala 47:17 nextpc.scala 51:17 nextpc.scala 55:15 nextpc.scala 59:15]
  assign io_taken = io_branch ? _T_25 : potato6; // @[nextpc.scala 48:16 nextpc.scala 52:16 nextpc.scala 57:14 nextpc.scala 60:14]
endmodule
module Adder(
  input  [63:0] io_inputx,
  output [63:0] io_result
);
  assign io_result = io_inputx + 64'h4; // @[helpers.scala 24:13]
endmodule
module ForwardingUnit(
  input  [4:0] io_rs1,
  input  [4:0] io_rs2,
  input  [4:0] io_exmemrd,
  input        io_exmemrw,
  input  [4:0] io_memwbrd,
  input        io_memwbrw,
  output [1:0] io_forwardA,
  output [1:0] io_forwardB
);
  wire  _T_1 = io_memwbrd == io_rs1; // @[forwarding.scala 39:53]
  wire  _T_2 = io_memwbrw & _T_1; // @[forwarding.scala 39:39]
  wire  _T_3 = io_memwbrd != 5'h0; // @[forwarding.scala 39:78]
  wire  potato5 = _T_2 & _T_3; // @[forwarding.scala 39:64]
  wire  _T_5 = io_exmemrd == io_rs1; // @[forwarding.scala 41:53]
  wire  potato8 = io_exmemrw & _T_5; // @[forwarding.scala 41:39]
  wire  _T_6 = io_exmemrd != 5'h0; // @[forwarding.scala 43:31]
  wire  _T_7 = potato8 & _T_6; // @[forwarding.scala 43:17]
  wire [1:0] _GEN_0 = potato5 ? 2'h2 : 2'h0; // @[forwarding.scala 46:23]
  wire  _T_9 = io_exmemrd == io_rs2; // @[forwarding.scala 53:45]
  wire  _T_10 = io_exmemrw & _T_9; // @[forwarding.scala 53:31]
  wire  _T_12 = _T_10 & _T_6; // @[forwarding.scala 53:56]
  wire  _T_14 = io_memwbrd == io_rs2; // @[forwarding.scala 56:50]
  wire  _T_15 = io_memwbrw & _T_14; // @[forwarding.scala 56:36]
  wire  _T_17 = _T_15 & _T_3; // @[forwarding.scala 56:61]
  wire [1:0] _GEN_2 = _T_17 ? 2'h2 : 2'h0; // @[forwarding.scala 56:84]
  assign io_forwardA = _T_7 ? 2'h1 : _GEN_0; // @[forwarding.scala 44:17 forwarding.scala 47:17 forwarding.scala 50:17]
  assign io_forwardB = _T_12 ? 2'h1 : _GEN_2; // @[forwarding.scala 54:17 forwarding.scala 57:17 forwarding.scala 60:17]
endmodule
module HazardUnit(
  input  [4:0] io_rs1,
  input  [4:0] io_rs2,
  input        io_idex_memread,
  input  [4:0] io_idex_rd,
  input        io_exmem_taken,
  output       io_pcfromtaken,
  output       io_pcstall,
  output       io_if_id_stall,
  output       io_id_ex_flush,
  output       io_ex_mem_flush,
  output       io_if_id_flush
);
  wire  _T = io_idex_rd == io_rs1; // @[hazard.scala 58:47]
  wire  _T_1 = io_idex_rd == io_rs2; // @[hazard.scala 58:72]
  wire  _T_2 = _T | _T_1; // @[hazard.scala 58:58]
  wire  _T_3 = io_idex_memread & _T_2; // @[hazard.scala 58:32]
  assign io_pcfromtaken = io_exmem_taken; // @[hazard.scala 44:19 hazard.scala 52:21 hazard.scala 59:21]
  assign io_pcstall = io_exmem_taken ? 1'h0 : _T_3; // @[hazard.scala 45:19 hazard.scala 53:21 hazard.scala 60:21]
  assign io_if_id_stall = io_exmem_taken ? 1'h0 : _T_3; // @[hazard.scala 46:19 hazard.scala 54:21 hazard.scala 61:21]
  assign io_id_ex_flush = io_exmem_taken | _T_3; // @[hazard.scala 47:19 hazard.scala 56:21 hazard.scala 62:21]
  assign io_ex_mem_flush = io_exmem_taken; // @[hazard.scala 48:19 hazard.scala 57:21 hazard.scala 63:21]
  assign io_if_id_flush = io_exmem_taken; // @[hazard.scala 49:19 hazard.scala 55:21 hazard.scala 64:21]
endmodule
module StageReg(
  input         clock,
  input         reset,
  input  [31:0] io_in_instruction,
  input  [63:0] io_in_pc,
  input         io_flush,
  input         io_valid,
  output [31:0] io_data_instruction,
  output [63:0] io_data_pc
);
  reg [31:0] reg_instruction; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_0;
  reg [63:0] reg_pc; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_1;
  assign io_data_instruction = reg_instruction; // @[stage-register.scala 46:11]
  assign io_data_pc = reg_pc; // @[stage-register.scala 46:11]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  reg_instruction = _RAND_0[31:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {2{`RANDOM}};
  reg_pc = _RAND_1[63:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      reg_instruction <= 32'h0;
    end else if (io_flush) begin
      reg_instruction <= 32'h0;
    end else if (io_valid) begin
      reg_instruction <= io_in_instruction;
    end
    if (reset) begin
      reg_pc <= 64'h0;
    end else if (io_flush) begin
      reg_pc <= 64'h0;
    end else if (io_valid) begin
      reg_pc <= io_in_pc;
    end
  end
endmodule
module StageReg_1(
  input         clock,
  input         reset,
  input  [63:0] io_in_pc,
  input  [63:0] io_in_instruction,
  input  [63:0] io_in_sextImm,
  input  [63:0] io_in_readdata1,
  input  [63:0] io_in_readdata2,
  input         io_flush,
  output [63:0] io_data_pc,
  output [63:0] io_data_instruction,
  output [63:0] io_data_sextImm,
  output [63:0] io_data_readdata1,
  output [63:0] io_data_readdata2
);
  reg [63:0] reg_pc; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_0;
  reg [63:0] reg_instruction; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_1;
  reg [63:0] reg_sextImm; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_2;
  reg [63:0] reg_readdata1; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_3;
  reg [63:0] reg_readdata2; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_4;
  assign io_data_pc = reg_pc; // @[stage-register.scala 46:11]
  assign io_data_instruction = reg_instruction; // @[stage-register.scala 46:11]
  assign io_data_sextImm = reg_sextImm; // @[stage-register.scala 46:11]
  assign io_data_readdata1 = reg_readdata1; // @[stage-register.scala 46:11]
  assign io_data_readdata2 = reg_readdata2; // @[stage-register.scala 46:11]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {2{`RANDOM}};
  reg_pc = _RAND_0[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {2{`RANDOM}};
  reg_instruction = _RAND_1[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {2{`RANDOM}};
  reg_sextImm = _RAND_2[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {2{`RANDOM}};
  reg_readdata1 = _RAND_3[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {2{`RANDOM}};
  reg_readdata2 = _RAND_4[63:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      reg_pc <= 64'h0;
    end else if (io_flush) begin
      reg_pc <= 64'h0;
    end else begin
      reg_pc <= io_in_pc;
    end
    if (reset) begin
      reg_instruction <= 64'h0;
    end else if (io_flush) begin
      reg_instruction <= 64'h0;
    end else begin
      reg_instruction <= io_in_instruction;
    end
    if (reset) begin
      reg_sextImm <= 64'h0;
    end else if (io_flush) begin
      reg_sextImm <= 64'h0;
    end else begin
      reg_sextImm <= io_in_sextImm;
    end
    if (reset) begin
      reg_readdata1 <= 64'h0;
    end else if (io_flush) begin
      reg_readdata1 <= 64'h0;
    end else begin
      reg_readdata1 <= io_in_readdata1;
    end
    if (reset) begin
      reg_readdata2 <= 64'h0;
    end else if (io_flush) begin
      reg_readdata2 <= 64'h0;
    end else begin
      reg_readdata2 <= io_in_readdata2;
    end
  end
endmodule
module StageReg_2(
  input        clock,
  input        reset,
  input        io_in_ex_ctrl_itype,
  input        io_in_ex_ctrl_aluop,
  input        io_in_ex_ctrl_src1,
  input  [1:0] io_in_ex_ctrl_src2,
  input        io_in_ex_ctrl_branch,
  input  [1:0] io_in_ex_ctrl_jumptype,
  input        io_in_ex_ctrl_resultselect,
  input        io_in_ex_ctrl_wordinst,
  input  [1:0] io_in_mem_ctrl_memop,
  input        io_in_wb_ctrl_toreg,
  input        io_in_wb_ctrl_regwrite,
  input        io_flush,
  output       io_data_ex_ctrl_itype,
  output       io_data_ex_ctrl_aluop,
  output       io_data_ex_ctrl_src1,
  output [1:0] io_data_ex_ctrl_src2,
  output       io_data_ex_ctrl_branch,
  output [1:0] io_data_ex_ctrl_jumptype,
  output       io_data_ex_ctrl_resultselect,
  output       io_data_ex_ctrl_wordinst,
  output [1:0] io_data_mem_ctrl_memop,
  output       io_data_wb_ctrl_toreg,
  output       io_data_wb_ctrl_regwrite
);
  reg  reg_ex_ctrl_itype; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_0;
  reg  reg_ex_ctrl_aluop; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_1;
  reg  reg_ex_ctrl_src1; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_2;
  reg [1:0] reg_ex_ctrl_src2; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_3;
  reg  reg_ex_ctrl_branch; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_4;
  reg [1:0] reg_ex_ctrl_jumptype; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_5;
  reg  reg_ex_ctrl_resultselect; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_6;
  reg  reg_ex_ctrl_wordinst; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_7;
  reg [1:0] reg_mem_ctrl_memop; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_8;
  reg  reg_wb_ctrl_toreg; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_9;
  reg  reg_wb_ctrl_regwrite; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_10;
  assign io_data_ex_ctrl_itype = reg_ex_ctrl_itype; // @[stage-register.scala 46:11]
  assign io_data_ex_ctrl_aluop = reg_ex_ctrl_aluop; // @[stage-register.scala 46:11]
  assign io_data_ex_ctrl_src1 = reg_ex_ctrl_src1; // @[stage-register.scala 46:11]
  assign io_data_ex_ctrl_src2 = reg_ex_ctrl_src2; // @[stage-register.scala 46:11]
  assign io_data_ex_ctrl_branch = reg_ex_ctrl_branch; // @[stage-register.scala 46:11]
  assign io_data_ex_ctrl_jumptype = reg_ex_ctrl_jumptype; // @[stage-register.scala 46:11]
  assign io_data_ex_ctrl_resultselect = reg_ex_ctrl_resultselect; // @[stage-register.scala 46:11]
  assign io_data_ex_ctrl_wordinst = reg_ex_ctrl_wordinst; // @[stage-register.scala 46:11]
  assign io_data_mem_ctrl_memop = reg_mem_ctrl_memop; // @[stage-register.scala 46:11]
  assign io_data_wb_ctrl_toreg = reg_wb_ctrl_toreg; // @[stage-register.scala 46:11]
  assign io_data_wb_ctrl_regwrite = reg_wb_ctrl_regwrite; // @[stage-register.scala 46:11]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  reg_ex_ctrl_itype = _RAND_0[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  reg_ex_ctrl_aluop = _RAND_1[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  reg_ex_ctrl_src1 = _RAND_2[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {1{`RANDOM}};
  reg_ex_ctrl_src2 = _RAND_3[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {1{`RANDOM}};
  reg_ex_ctrl_branch = _RAND_4[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {1{`RANDOM}};
  reg_ex_ctrl_jumptype = _RAND_5[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_6 = {1{`RANDOM}};
  reg_ex_ctrl_resultselect = _RAND_6[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_7 = {1{`RANDOM}};
  reg_ex_ctrl_wordinst = _RAND_7[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_8 = {1{`RANDOM}};
  reg_mem_ctrl_memop = _RAND_8[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_9 = {1{`RANDOM}};
  reg_wb_ctrl_toreg = _RAND_9[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_10 = {1{`RANDOM}};
  reg_wb_ctrl_regwrite = _RAND_10[0:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      reg_ex_ctrl_itype <= 1'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_itype <= 1'h0;
    end else begin
      reg_ex_ctrl_itype <= io_in_ex_ctrl_itype;
    end
    if (reset) begin
      reg_ex_ctrl_aluop <= 1'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_aluop <= 1'h0;
    end else begin
      reg_ex_ctrl_aluop <= io_in_ex_ctrl_aluop;
    end
    if (reset) begin
      reg_ex_ctrl_src1 <= 1'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_src1 <= 1'h0;
    end else begin
      reg_ex_ctrl_src1 <= io_in_ex_ctrl_src1;
    end
    if (reset) begin
      reg_ex_ctrl_src2 <= 2'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_src2 <= 2'h0;
    end else begin
      reg_ex_ctrl_src2 <= io_in_ex_ctrl_src2;
    end
    if (reset) begin
      reg_ex_ctrl_branch <= 1'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_branch <= 1'h0;
    end else begin
      reg_ex_ctrl_branch <= io_in_ex_ctrl_branch;
    end
    if (reset) begin
      reg_ex_ctrl_jumptype <= 2'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_jumptype <= 2'h0;
    end else begin
      reg_ex_ctrl_jumptype <= io_in_ex_ctrl_jumptype;
    end
    if (reset) begin
      reg_ex_ctrl_resultselect <= 1'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_resultselect <= 1'h0;
    end else begin
      reg_ex_ctrl_resultselect <= io_in_ex_ctrl_resultselect;
    end
    if (reset) begin
      reg_ex_ctrl_wordinst <= 1'h0;
    end else if (io_flush) begin
      reg_ex_ctrl_wordinst <= 1'h0;
    end else begin
      reg_ex_ctrl_wordinst <= io_in_ex_ctrl_wordinst;
    end
    if (reset) begin
      reg_mem_ctrl_memop <= 2'h0;
    end else if (io_flush) begin
      reg_mem_ctrl_memop <= 2'h0;
    end else begin
      reg_mem_ctrl_memop <= io_in_mem_ctrl_memop;
    end
    if (reset) begin
      reg_wb_ctrl_toreg <= 1'h0;
    end else if (io_flush) begin
      reg_wb_ctrl_toreg <= 1'h0;
    end else begin
      reg_wb_ctrl_toreg <= io_in_wb_ctrl_toreg;
    end
    if (reset) begin
      reg_wb_ctrl_regwrite <= 1'h0;
    end else if (io_flush) begin
      reg_wb_ctrl_regwrite <= 1'h0;
    end else begin
      reg_wb_ctrl_regwrite <= io_in_wb_ctrl_regwrite;
    end
  end
endmodule
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
  reg [63:0] reg_ex_result; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_0;
  reg [63:0] reg_mem_writedata; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_1;
  reg [63:0] reg_nextpc; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_2;
  reg  reg_taken; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_3;
  reg [63:0] reg_instruction; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_4;
  assign io_data_ex_result = reg_ex_result; // @[stage-register.scala 46:11]
  assign io_data_mem_writedata = reg_mem_writedata; // @[stage-register.scala 46:11]
  assign io_data_nextpc = reg_nextpc; // @[stage-register.scala 46:11]
  assign io_data_taken = reg_taken; // @[stage-register.scala 46:11]
  assign io_data_instruction = reg_instruction; // @[stage-register.scala 46:11]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {2{`RANDOM}};
  reg_ex_result = _RAND_0[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {2{`RANDOM}};
  reg_mem_writedata = _RAND_1[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {2{`RANDOM}};
  reg_nextpc = _RAND_2[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {1{`RANDOM}};
  reg_taken = _RAND_3[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_4 = {2{`RANDOM}};
  reg_instruction = _RAND_4[63:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      reg_ex_result <= 64'h0;
    end else if (io_flush) begin
      reg_ex_result <= 64'h0;
    end else begin
      reg_ex_result <= io_in_ex_result;
    end
    if (reset) begin
      reg_mem_writedata <= 64'h0;
    end else if (io_flush) begin
      reg_mem_writedata <= 64'h0;
    end else begin
      reg_mem_writedata <= io_in_mem_writedata;
    end
    if (reset) begin
      reg_nextpc <= 64'h0;
    end else if (io_flush) begin
      reg_nextpc <= 64'h0;
    end else begin
      reg_nextpc <= io_in_nextpc;
    end
    if (reset) begin
      reg_taken <= 1'h0;
    end else if (io_flush) begin
      reg_taken <= 1'h0;
    end else begin
      reg_taken <= io_in_taken;
    end
    if (reset) begin
      reg_instruction <= 64'h0;
    end else if (io_flush) begin
      reg_instruction <= 64'h0;
    end else begin
      reg_instruction <= io_in_instruction;
    end
  end
endmodule
module StageReg_4(
  input        clock,
  input        reset,
  input  [1:0] io_in_mem_ctrl_memop,
  input        io_in_wb_ctrl_toreg,
  input        io_in_wb_ctrl_regwrite,
  input        io_flush,
  output [1:0] io_data_mem_ctrl_memop,
  output       io_data_wb_ctrl_toreg,
  output       io_data_wb_ctrl_regwrite
);
  reg [1:0] reg_mem_ctrl_memop; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_0;
  reg  reg_wb_ctrl_toreg; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_1;
  reg  reg_wb_ctrl_regwrite; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_2;
  assign io_data_mem_ctrl_memop = reg_mem_ctrl_memop; // @[stage-register.scala 46:11]
  assign io_data_wb_ctrl_toreg = reg_wb_ctrl_toreg; // @[stage-register.scala 46:11]
  assign io_data_wb_ctrl_regwrite = reg_wb_ctrl_regwrite; // @[stage-register.scala 46:11]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  reg_mem_ctrl_memop = _RAND_0[1:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  reg_wb_ctrl_toreg = _RAND_1[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  reg_wb_ctrl_regwrite = _RAND_2[0:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      reg_mem_ctrl_memop <= 2'h0;
    end else if (io_flush) begin
      reg_mem_ctrl_memop <= 2'h0;
    end else begin
      reg_mem_ctrl_memop <= io_in_mem_ctrl_memop;
    end
    if (reset) begin
      reg_wb_ctrl_toreg <= 1'h0;
    end else if (io_flush) begin
      reg_wb_ctrl_toreg <= 1'h0;
    end else begin
      reg_wb_ctrl_toreg <= io_in_wb_ctrl_toreg;
    end
    if (reset) begin
      reg_wb_ctrl_regwrite <= 1'h0;
    end else if (io_flush) begin
      reg_wb_ctrl_regwrite <= 1'h0;
    end else begin
      reg_wb_ctrl_regwrite <= io_in_wb_ctrl_regwrite;
    end
  end
endmodule
module StageReg_5(
  input         clock,
  input         reset,
  input  [63:0] io_in_readdata,
  input  [63:0] io_in_ex_result,
  input  [63:0] io_in_instruction,
  output [63:0] io_data_readdata,
  output [63:0] io_data_ex_result,
  output [63:0] io_data_instruction
);
  reg [63:0] reg_readdata; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_0;
  reg [63:0] reg_ex_result; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_1;
  reg [63:0] reg_instruction; // @[stage-register.scala 44:21]
  reg [63:0] _RAND_2;
  assign io_data_readdata = reg_readdata; // @[stage-register.scala 46:11]
  assign io_data_ex_result = reg_ex_result; // @[stage-register.scala 46:11]
  assign io_data_instruction = reg_instruction; // @[stage-register.scala 46:11]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {2{`RANDOM}};
  reg_readdata = _RAND_0[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {2{`RANDOM}};
  reg_ex_result = _RAND_1[63:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {2{`RANDOM}};
  reg_instruction = _RAND_2[63:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      reg_readdata <= 64'h0;
    end else begin
      reg_readdata <= io_in_readdata;
    end
    if (reset) begin
      reg_ex_result <= 64'h0;
    end else begin
      reg_ex_result <= io_in_ex_result;
    end
    if (reset) begin
      reg_instruction <= 64'h0;
    end else begin
      reg_instruction <= io_in_instruction;
    end
  end
endmodule
module StageReg_6(
  input   clock,
  input   reset,
  input   io_in_wb_ctrl_toreg,
  input   io_in_wb_ctrl_regwrite,
  output  io_data_wb_ctrl_toreg,
  output  io_data_wb_ctrl_regwrite
);
  reg  reg_wb_ctrl_toreg; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_0;
  reg  reg_wb_ctrl_regwrite; // @[stage-register.scala 44:21]
  reg [31:0] _RAND_1;
  assign io_data_wb_ctrl_toreg = reg_wb_ctrl_toreg; // @[stage-register.scala 46:11]
  assign io_data_wb_ctrl_regwrite = reg_wb_ctrl_regwrite; // @[stage-register.scala 46:11]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  reg_wb_ctrl_toreg = _RAND_0[0:0];
  `endif // RANDOMIZE_REG_INIT
  `ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  reg_wb_ctrl_regwrite = _RAND_1[0:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      reg_wb_ctrl_toreg <= 1'h0;
    end else begin
      reg_wb_ctrl_toreg <= io_in_wb_ctrl_toreg;
    end
    if (reset) begin
      reg_wb_ctrl_regwrite <= 1'h0;
    end else begin
      reg_wb_ctrl_regwrite <= io_in_wb_ctrl_regwrite;
    end
  end
endmodule
module PipelinedCPU(
  input         clock,
  input         reset,
  output [63:0] io_imem_address,
  output        io_imem_valid,
  input         io_imem_good,
  input  [63:0] io_imem_instruction,
  input         io_imem_ready,
  output [63:0] io_dmem_address,
  output        io_dmem_valid,
  input         io_dmem_good,
  output [63:0] io_dmem_writedata,
  output        io_dmem_memread,
  output        io_dmem_memwrite,
  output [1:0]  io_dmem_maskmode,
  output        io_dmem_sext,
  input  [63:0] io_dmem_readdata
);
  wire [6:0] control_io_opcode; // @[cpu.scala 92:31]
  wire  control_io_itype; // @[cpu.scala 92:31]
  wire  control_io_aluop; // @[cpu.scala 92:31]
  wire  control_io_src1; // @[cpu.scala 92:31]
  wire [1:0] control_io_src2; // @[cpu.scala 92:31]
  wire  control_io_branch; // @[cpu.scala 92:31]
  wire [1:0] control_io_jumptype; // @[cpu.scala 92:31]
  wire  control_io_resultselect; // @[cpu.scala 92:31]
  wire [1:0] control_io_memop; // @[cpu.scala 92:31]
  wire  control_io_toreg; // @[cpu.scala 92:31]
  wire  control_io_regwrite; // @[cpu.scala 92:31]
  wire  control_io_wordinst; // @[cpu.scala 92:31]
  wire  registers_clock; // @[cpu.scala 93:31]
  wire [4:0] registers_io_readreg1; // @[cpu.scala 93:31]
  wire [4:0] registers_io_readreg2; // @[cpu.scala 93:31]
  wire [4:0] registers_io_writereg; // @[cpu.scala 93:31]
  wire [63:0] registers_io_writedata; // @[cpu.scala 93:31]
  wire  registers_io_wen; // @[cpu.scala 93:31]
  wire [63:0] registers_io_readdata1; // @[cpu.scala 93:31]
  wire [63:0] registers_io_readdata2; // @[cpu.scala 93:31]
  wire  aluControl_io_aluop; // @[cpu.scala 94:31]
  wire  aluControl_io_itype; // @[cpu.scala 94:31]
  wire [6:0] aluControl_io_funct7; // @[cpu.scala 94:31]
  wire [2:0] aluControl_io_funct3; // @[cpu.scala 94:31]
  wire  aluControl_io_wordinst; // @[cpu.scala 94:31]
  wire [4:0] aluControl_io_operation; // @[cpu.scala 94:31]
  wire [4:0] alu_io_operation; // @[cpu.scala 95:31]
  wire [63:0] alu_io_inputx; // @[cpu.scala 95:31]
  wire [63:0] alu_io_inputy; // @[cpu.scala 95:31]
  wire [63:0] alu_io_result; // @[cpu.scala 95:31]
  wire [63:0] immGen_io_instruction; // @[cpu.scala 96:31]
  wire [63:0] immGen_io_sextImm; // @[cpu.scala 96:31]
  wire  nextPCmod_io_branch; // @[cpu.scala 97:31]
  wire [1:0] nextPCmod_io_jumptype; // @[cpu.scala 97:31]
  wire [63:0] nextPCmod_io_inputx; // @[cpu.scala 97:31]
  wire [63:0] nextPCmod_io_inputy; // @[cpu.scala 97:31]
  wire [2:0] nextPCmod_io_funct3; // @[cpu.scala 97:31]
  wire [63:0] nextPCmod_io_pc; // @[cpu.scala 97:31]
  wire [63:0] nextPCmod_io_imm; // @[cpu.scala 97:31]
  wire [63:0] nextPCmod_io_nextpc; // @[cpu.scala 97:31]
  wire  nextPCmod_io_taken; // @[cpu.scala 97:31]
  wire [63:0] pcPlusFour_io_inputx; // @[cpu.scala 98:31]
  wire [63:0] pcPlusFour_io_result; // @[cpu.scala 98:31]
  wire [4:0] forwarding_io_rs1; // @[cpu.scala 99:31]
  wire [4:0] forwarding_io_rs2; // @[cpu.scala 99:31]
  wire [4:0] forwarding_io_exmemrd; // @[cpu.scala 99:31]
  wire  forwarding_io_exmemrw; // @[cpu.scala 99:31]
  wire [4:0] forwarding_io_memwbrd; // @[cpu.scala 99:31]
  wire  forwarding_io_memwbrw; // @[cpu.scala 99:31]
  wire [1:0] forwarding_io_forwardA; // @[cpu.scala 99:31]
  wire [1:0] forwarding_io_forwardB; // @[cpu.scala 99:31]
  wire [4:0] hazard_io_rs1; // @[cpu.scala 100:31]
  wire [4:0] hazard_io_rs2; // @[cpu.scala 100:31]
  wire  hazard_io_idex_memread; // @[cpu.scala 100:31]
  wire [4:0] hazard_io_idex_rd; // @[cpu.scala 100:31]
  wire  hazard_io_exmem_taken; // @[cpu.scala 100:31]
  wire  hazard_io_pcfromtaken; // @[cpu.scala 100:31]
  wire  hazard_io_pcstall; // @[cpu.scala 100:31]
  wire  hazard_io_if_id_stall; // @[cpu.scala 100:31]
  wire  hazard_io_id_ex_flush; // @[cpu.scala 100:31]
  wire  hazard_io_ex_mem_flush; // @[cpu.scala 100:31]
  wire  hazard_io_if_id_flush; // @[cpu.scala 100:31]
  wire  if_id_clock; // @[cpu.scala 104:27]
  wire  if_id_reset; // @[cpu.scala 104:27]
  wire [31:0] if_id_io_in_instruction; // @[cpu.scala 104:27]
  wire [63:0] if_id_io_in_pc; // @[cpu.scala 104:27]
  wire  if_id_io_flush; // @[cpu.scala 104:27]
  wire  if_id_io_valid; // @[cpu.scala 104:27]
  wire [31:0] if_id_io_data_instruction; // @[cpu.scala 104:27]
  wire [63:0] if_id_io_data_pc; // @[cpu.scala 104:27]
  wire  id_ex_clock; // @[cpu.scala 106:27]
  wire  id_ex_reset; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_in_pc; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_in_instruction; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_in_sextImm; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_in_readdata1; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_in_readdata2; // @[cpu.scala 106:27]
  wire  id_ex_io_flush; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_data_pc; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_data_instruction; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_data_sextImm; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_data_readdata1; // @[cpu.scala 106:27]
  wire [63:0] id_ex_io_data_readdata2; // @[cpu.scala 106:27]
  wire  id_ex_ctrl_clock; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_reset; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_ex_ctrl_itype; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_ex_ctrl_aluop; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_ex_ctrl_src1; // @[cpu.scala 107:27]
  wire [1:0] id_ex_ctrl_io_in_ex_ctrl_src2; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_ex_ctrl_branch; // @[cpu.scala 107:27]
  wire [1:0] id_ex_ctrl_io_in_ex_ctrl_jumptype; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_ex_ctrl_resultselect; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_ex_ctrl_wordinst; // @[cpu.scala 107:27]
  wire [1:0] id_ex_ctrl_io_in_mem_ctrl_memop; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_wb_ctrl_toreg; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_in_wb_ctrl_regwrite; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_flush; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_ex_ctrl_itype; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_ex_ctrl_aluop; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_ex_ctrl_src1; // @[cpu.scala 107:27]
  wire [1:0] id_ex_ctrl_io_data_ex_ctrl_src2; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_ex_ctrl_branch; // @[cpu.scala 107:27]
  wire [1:0] id_ex_ctrl_io_data_ex_ctrl_jumptype; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_ex_ctrl_resultselect; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_ex_ctrl_wordinst; // @[cpu.scala 107:27]
  wire [1:0] id_ex_ctrl_io_data_mem_ctrl_memop; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_wb_ctrl_toreg; // @[cpu.scala 107:27]
  wire  id_ex_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 107:27]
  wire  ex_mem_clock; // @[cpu.scala 109:27]
  wire  ex_mem_reset; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_in_ex_result; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_in_mem_writedata; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_in_nextpc; // @[cpu.scala 109:27]
  wire  ex_mem_io_in_taken; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_in_instruction; // @[cpu.scala 109:27]
  wire  ex_mem_io_flush; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_data_ex_result; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_data_mem_writedata; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_data_nextpc; // @[cpu.scala 109:27]
  wire  ex_mem_io_data_taken; // @[cpu.scala 109:27]
  wire [63:0] ex_mem_io_data_instruction; // @[cpu.scala 109:27]
  wire  ex_mem_ctrl_clock; // @[cpu.scala 110:27]
  wire  ex_mem_ctrl_reset; // @[cpu.scala 110:27]
  wire [1:0] ex_mem_ctrl_io_in_mem_ctrl_memop; // @[cpu.scala 110:27]
  wire  ex_mem_ctrl_io_in_wb_ctrl_toreg; // @[cpu.scala 110:27]
  wire  ex_mem_ctrl_io_in_wb_ctrl_regwrite; // @[cpu.scala 110:27]
  wire  ex_mem_ctrl_io_flush; // @[cpu.scala 110:27]
  wire [1:0] ex_mem_ctrl_io_data_mem_ctrl_memop; // @[cpu.scala 110:27]
  wire  ex_mem_ctrl_io_data_wb_ctrl_toreg; // @[cpu.scala 110:27]
  wire  ex_mem_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 110:27]
  wire  mem_wb_clock; // @[cpu.scala 112:27]
  wire  mem_wb_reset; // @[cpu.scala 112:27]
  wire [63:0] mem_wb_io_in_readdata; // @[cpu.scala 112:27]
  wire [63:0] mem_wb_io_in_ex_result; // @[cpu.scala 112:27]
  wire [63:0] mem_wb_io_in_instruction; // @[cpu.scala 112:27]
  wire [63:0] mem_wb_io_data_readdata; // @[cpu.scala 112:27]
  wire [63:0] mem_wb_io_data_ex_result; // @[cpu.scala 112:27]
  wire [63:0] mem_wb_io_data_instruction; // @[cpu.scala 112:27]
  wire  mem_wb_ctrl_clock; // @[cpu.scala 115:27]
  wire  mem_wb_ctrl_reset; // @[cpu.scala 115:27]
  wire  mem_wb_ctrl_io_in_wb_ctrl_toreg; // @[cpu.scala 115:27]
  wire  mem_wb_ctrl_io_in_wb_ctrl_regwrite; // @[cpu.scala 115:27]
  wire  mem_wb_ctrl_io_data_wb_ctrl_toreg; // @[cpu.scala 115:27]
  wire  mem_wb_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 115:27]
  reg [63:0] pc; // @[cpu.scala 91:32]
  reg [63:0] _RAND_0;
  wire [63:0] next_pc = ex_mem_io_data_nextpc; // @[cpu.scala 121:21 cpu.scala 317:11]
  wire [63:0] _GEN_0 = pc % 64'h8; // @[cpu.scala 145:22]
  wire [3:0] _T_4 = _GEN_0[3:0]; // @[cpu.scala 145:22]
  wire  potato1 = _T_4 == 4'h4; // @[cpu.scala 145:29]
  wire  _T_12 = forwarding_io_forwardA == 2'h0; // @[cpu.scala 249:69]
  wire  _T_13 = forwarding_io_forwardA == 2'h1; // @[cpu.scala 250:69]
  wire  _T_14 = forwarding_io_forwardA == 2'h2; // @[cpu.scala 251:69]
  wire [63:0] wb_writedata = mem_wb_ctrl_io_data_wb_ctrl_toreg ? mem_wb_io_data_readdata : mem_wb_io_data_ex_result; // @[cpu.scala 351:32]
  wire [63:0] _T_15 = _T_14 ? wb_writedata : 64'h0; // @[Mux.scala 87:16]
  wire [63:0] _T_16 = _T_13 ? ex_mem_io_data_ex_result : _T_15; // @[Mux.scala 87:16]
  wire [63:0] forwarded_inputx = _T_12 ? id_ex_io_data_readdata1 : _T_16; // @[Mux.scala 87:16]
  wire  _T_17 = forwarding_io_forwardB == 2'h0; // @[cpu.scala 253:69]
  wire  _T_18 = forwarding_io_forwardB == 2'h1; // @[cpu.scala 254:69]
  wire  _T_19 = forwarding_io_forwardB == 2'h2; // @[cpu.scala 255:69]
  wire [63:0] _T_20 = _T_19 ? wb_writedata : 64'h0; // @[Mux.scala 87:16]
  wire [63:0] _T_21 = _T_18 ? ex_mem_io_data_ex_result : _T_20; // @[Mux.scala 87:16]
  wire [63:0] forwarded_inputy = _T_17 ? id_ex_io_data_readdata2 : _T_21; // @[Mux.scala 87:16]
  wire  _T_22 = id_ex_ctrl_io_data_ex_ctrl_src2 == 2'h0; // @[cpu.scala 260:71]
  wire  _T_23 = id_ex_ctrl_io_data_ex_ctrl_src2 == 2'h1; // @[cpu.scala 261:71]
  wire  _T_24 = id_ex_ctrl_io_data_ex_ctrl_src2 == 2'h2; // @[cpu.scala 262:71]
  wire [2:0] _T_25 = _T_24 ? 3'h4 : 3'h0; // @[Mux.scala 87:16]
  wire [63:0] _T_26 = _T_23 ? id_ex_io_data_sextImm : {{61'd0}, _T_25}; // @[Mux.scala 87:16]
  wire [2:0] mem_funct3 = ex_mem_io_data_instruction[14:12]; // @[cpu.scala 303:46]
  wire  _T_35 = mem_wb_io_data_instruction[11:7] != 5'h0; // @[cpu.scala 348:30]
  wire  _T_36 = mem_wb_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 348:79]
  Control control ( // @[cpu.scala 92:31]
    .io_opcode(control_io_opcode),
    .io_itype(control_io_itype),
    .io_aluop(control_io_aluop),
    .io_src1(control_io_src1),
    .io_src2(control_io_src2),
    .io_branch(control_io_branch),
    .io_jumptype(control_io_jumptype),
    .io_resultselect(control_io_resultselect),
    .io_memop(control_io_memop),
    .io_toreg(control_io_toreg),
    .io_regwrite(control_io_regwrite),
    .io_wordinst(control_io_wordinst)
  );
  RegisterFile registers ( // @[cpu.scala 93:31]
    .clock(registers_clock),
    .io_readreg1(registers_io_readreg1),
    .io_readreg2(registers_io_readreg2),
    .io_writereg(registers_io_writereg),
    .io_writedata(registers_io_writedata),
    .io_wen(registers_io_wen),
    .io_readdata1(registers_io_readdata1),
    .io_readdata2(registers_io_readdata2)
  );
  ALUControl aluControl ( // @[cpu.scala 94:31]
    .io_aluop(aluControl_io_aluop),
    .io_itype(aluControl_io_itype),
    .io_funct7(aluControl_io_funct7),
    .io_funct3(aluControl_io_funct3),
    .io_wordinst(aluControl_io_wordinst),
    .io_operation(aluControl_io_operation)
  );
  ALU alu ( // @[cpu.scala 95:31]
    .io_operation(alu_io_operation),
    .io_inputx(alu_io_inputx),
    .io_inputy(alu_io_inputy),
    .io_result(alu_io_result)
  );
  ImmediateGenerator immGen ( // @[cpu.scala 96:31]
    .io_instruction(immGen_io_instruction),
    .io_sextImm(immGen_io_sextImm)
  );
  NextPC nextPCmod ( // @[cpu.scala 97:31]
    .io_branch(nextPCmod_io_branch),
    .io_jumptype(nextPCmod_io_jumptype),
    .io_inputx(nextPCmod_io_inputx),
    .io_inputy(nextPCmod_io_inputy),
    .io_funct3(nextPCmod_io_funct3),
    .io_pc(nextPCmod_io_pc),
    .io_imm(nextPCmod_io_imm),
    .io_nextpc(nextPCmod_io_nextpc),
    .io_taken(nextPCmod_io_taken)
  );
  Adder pcPlusFour ( // @[cpu.scala 98:31]
    .io_inputx(pcPlusFour_io_inputx),
    .io_result(pcPlusFour_io_result)
  );
  ForwardingUnit forwarding ( // @[cpu.scala 99:31]
    .io_rs1(forwarding_io_rs1),
    .io_rs2(forwarding_io_rs2),
    .io_exmemrd(forwarding_io_exmemrd),
    .io_exmemrw(forwarding_io_exmemrw),
    .io_memwbrd(forwarding_io_memwbrd),
    .io_memwbrw(forwarding_io_memwbrw),
    .io_forwardA(forwarding_io_forwardA),
    .io_forwardB(forwarding_io_forwardB)
  );
  HazardUnit hazard ( // @[cpu.scala 100:31]
    .io_rs1(hazard_io_rs1),
    .io_rs2(hazard_io_rs2),
    .io_idex_memread(hazard_io_idex_memread),
    .io_idex_rd(hazard_io_idex_rd),
    .io_exmem_taken(hazard_io_exmem_taken),
    .io_pcfromtaken(hazard_io_pcfromtaken),
    .io_pcstall(hazard_io_pcstall),
    .io_if_id_stall(hazard_io_if_id_stall),
    .io_id_ex_flush(hazard_io_id_ex_flush),
    .io_ex_mem_flush(hazard_io_ex_mem_flush),
    .io_if_id_flush(hazard_io_if_id_flush)
  );
  StageReg if_id ( // @[cpu.scala 104:27]
    .clock(if_id_clock),
    .reset(if_id_reset),
    .io_in_instruction(if_id_io_in_instruction),
    .io_in_pc(if_id_io_in_pc),
    .io_flush(if_id_io_flush),
    .io_valid(if_id_io_valid),
    .io_data_instruction(if_id_io_data_instruction),
    .io_data_pc(if_id_io_data_pc)
  );
  StageReg_1 id_ex ( // @[cpu.scala 106:27]
    .clock(id_ex_clock),
    .reset(id_ex_reset),
    .io_in_pc(id_ex_io_in_pc),
    .io_in_instruction(id_ex_io_in_instruction),
    .io_in_sextImm(id_ex_io_in_sextImm),
    .io_in_readdata1(id_ex_io_in_readdata1),
    .io_in_readdata2(id_ex_io_in_readdata2),
    .io_flush(id_ex_io_flush),
    .io_data_pc(id_ex_io_data_pc),
    .io_data_instruction(id_ex_io_data_instruction),
    .io_data_sextImm(id_ex_io_data_sextImm),
    .io_data_readdata1(id_ex_io_data_readdata1),
    .io_data_readdata2(id_ex_io_data_readdata2)
  );
  StageReg_2 id_ex_ctrl ( // @[cpu.scala 107:27]
    .clock(id_ex_ctrl_clock),
    .reset(id_ex_ctrl_reset),
    .io_in_ex_ctrl_itype(id_ex_ctrl_io_in_ex_ctrl_itype),
    .io_in_ex_ctrl_aluop(id_ex_ctrl_io_in_ex_ctrl_aluop),
    .io_in_ex_ctrl_src1(id_ex_ctrl_io_in_ex_ctrl_src1),
    .io_in_ex_ctrl_src2(id_ex_ctrl_io_in_ex_ctrl_src2),
    .io_in_ex_ctrl_branch(id_ex_ctrl_io_in_ex_ctrl_branch),
    .io_in_ex_ctrl_jumptype(id_ex_ctrl_io_in_ex_ctrl_jumptype),
    .io_in_ex_ctrl_resultselect(id_ex_ctrl_io_in_ex_ctrl_resultselect),
    .io_in_ex_ctrl_wordinst(id_ex_ctrl_io_in_ex_ctrl_wordinst),
    .io_in_mem_ctrl_memop(id_ex_ctrl_io_in_mem_ctrl_memop),
    .io_in_wb_ctrl_toreg(id_ex_ctrl_io_in_wb_ctrl_toreg),
    .io_in_wb_ctrl_regwrite(id_ex_ctrl_io_in_wb_ctrl_regwrite),
    .io_flush(id_ex_ctrl_io_flush),
    .io_data_ex_ctrl_itype(id_ex_ctrl_io_data_ex_ctrl_itype),
    .io_data_ex_ctrl_aluop(id_ex_ctrl_io_data_ex_ctrl_aluop),
    .io_data_ex_ctrl_src1(id_ex_ctrl_io_data_ex_ctrl_src1),
    .io_data_ex_ctrl_src2(id_ex_ctrl_io_data_ex_ctrl_src2),
    .io_data_ex_ctrl_branch(id_ex_ctrl_io_data_ex_ctrl_branch),
    .io_data_ex_ctrl_jumptype(id_ex_ctrl_io_data_ex_ctrl_jumptype),
    .io_data_ex_ctrl_resultselect(id_ex_ctrl_io_data_ex_ctrl_resultselect),
    .io_data_ex_ctrl_wordinst(id_ex_ctrl_io_data_ex_ctrl_wordinst),
    .io_data_mem_ctrl_memop(id_ex_ctrl_io_data_mem_ctrl_memop),
    .io_data_wb_ctrl_toreg(id_ex_ctrl_io_data_wb_ctrl_toreg),
    .io_data_wb_ctrl_regwrite(id_ex_ctrl_io_data_wb_ctrl_regwrite)
  );
  StageReg_3 ex_mem ( // @[cpu.scala 109:27]
    .clock(ex_mem_clock),
    .reset(ex_mem_reset),
    .io_in_ex_result(ex_mem_io_in_ex_result),
    .io_in_mem_writedata(ex_mem_io_in_mem_writedata),
    .io_in_nextpc(ex_mem_io_in_nextpc),
    .io_in_taken(ex_mem_io_in_taken),
    .io_in_instruction(ex_mem_io_in_instruction),
    .io_flush(ex_mem_io_flush),
    .io_data_ex_result(ex_mem_io_data_ex_result),
    .io_data_mem_writedata(ex_mem_io_data_mem_writedata),
    .io_data_nextpc(ex_mem_io_data_nextpc),
    .io_data_taken(ex_mem_io_data_taken),
    .io_data_instruction(ex_mem_io_data_instruction)
  );
  StageReg_4 ex_mem_ctrl ( // @[cpu.scala 110:27]
    .clock(ex_mem_ctrl_clock),
    .reset(ex_mem_ctrl_reset),
    .io_in_mem_ctrl_memop(ex_mem_ctrl_io_in_mem_ctrl_memop),
    .io_in_wb_ctrl_toreg(ex_mem_ctrl_io_in_wb_ctrl_toreg),
    .io_in_wb_ctrl_regwrite(ex_mem_ctrl_io_in_wb_ctrl_regwrite),
    .io_flush(ex_mem_ctrl_io_flush),
    .io_data_mem_ctrl_memop(ex_mem_ctrl_io_data_mem_ctrl_memop),
    .io_data_wb_ctrl_toreg(ex_mem_ctrl_io_data_wb_ctrl_toreg),
    .io_data_wb_ctrl_regwrite(ex_mem_ctrl_io_data_wb_ctrl_regwrite)
  );
  StageReg_5 mem_wb ( // @[cpu.scala 112:27]
    .clock(mem_wb_clock),
    .reset(mem_wb_reset),
    .io_in_readdata(mem_wb_io_in_readdata),
    .io_in_ex_result(mem_wb_io_in_ex_result),
    .io_in_instruction(mem_wb_io_in_instruction),
    .io_data_readdata(mem_wb_io_data_readdata),
    .io_data_ex_result(mem_wb_io_data_ex_result),
    .io_data_instruction(mem_wb_io_data_instruction)
  );
  StageReg_6 mem_wb_ctrl ( // @[cpu.scala 115:27]
    .clock(mem_wb_ctrl_clock),
    .reset(mem_wb_ctrl_reset),
    .io_in_wb_ctrl_toreg(mem_wb_ctrl_io_in_wb_ctrl_toreg),
    .io_in_wb_ctrl_regwrite(mem_wb_ctrl_io_in_wb_ctrl_regwrite),
    .io_data_wb_ctrl_toreg(mem_wb_ctrl_io_data_wb_ctrl_toreg),
    .io_data_wb_ctrl_regwrite(mem_wb_ctrl_io_data_wb_ctrl_regwrite)
  );
  assign io_imem_address = pc; // @[cpu.scala 141:19]
  assign io_imem_valid = 1'h1; // @[cpu.scala 142:19]
  assign io_dmem_address = ex_mem_io_data_ex_result; // @[cpu.scala 306:21]
  assign io_dmem_valid = ex_mem_ctrl_io_data_mem_ctrl_memop[1]; // @[cpu.scala 310:21]
  assign io_dmem_writedata = ex_mem_io_data_mem_writedata; // @[cpu.scala 314:21]
  assign io_dmem_memread = ~ex_mem_ctrl_io_data_mem_ctrl_memop[0]; // @[cpu.scala 307:21]
  assign io_dmem_memwrite = ex_mem_ctrl_io_data_mem_ctrl_memop[0]; // @[cpu.scala 309:21]
  assign io_dmem_maskmode = mem_funct3[1:0]; // @[cpu.scala 311:21]
  assign io_dmem_sext = ~mem_funct3[2]; // @[cpu.scala 312:21]
  assign control_io_opcode = if_id_io_data_instruction[6:0]; // @[cpu.scala 165:21]
  assign registers_clock = clock;
  assign registers_io_readreg1 = if_id_io_data_instruction[19:15]; // @[cpu.scala 176:25]
  assign registers_io_readreg2 = if_id_io_data_instruction[24:20]; // @[cpu.scala 177:25]
  assign registers_io_writereg = mem_wb_io_data_instruction[11:7]; // @[cpu.scala 345:25]
  assign registers_io_writedata = mem_wb_ctrl_io_data_wb_ctrl_toreg ? mem_wb_io_data_readdata : mem_wb_io_data_ex_result; // @[cpu.scala 353:26]
  assign registers_io_wen = _T_35 & _T_36; // @[cpu.scala 348:20]
  assign aluControl_io_aluop = id_ex_ctrl_io_data_ex_ctrl_aluop; // @[cpu.scala 238:26]
  assign aluControl_io_itype = id_ex_ctrl_io_data_ex_ctrl_itype; // @[cpu.scala 237:26]
  assign aluControl_io_funct7 = id_ex_io_data_instruction[31:25]; // @[cpu.scala 241:26]
  assign aluControl_io_funct3 = id_ex_io_data_instruction[14:12]; // @[cpu.scala 240:26]
  assign aluControl_io_wordinst = id_ex_ctrl_io_data_ex_ctrl_wordinst; // @[cpu.scala 239:26]
  assign alu_io_operation = aluControl_io_operation; // @[cpu.scala 265:21]
  assign alu_io_inputx = id_ex_ctrl_io_data_ex_ctrl_src1 ? id_ex_io_data_pc : forwarded_inputx; // @[cpu.scala 267:17]
  assign alu_io_inputy = _T_22 ? forwarded_inputy : _T_26; // @[cpu.scala 268:17]
  assign immGen_io_instruction = {{32'd0}, if_id_io_data_instruction}; // @[cpu.scala 180:25]
  assign nextPCmod_io_branch = id_ex_ctrl_io_data_ex_ctrl_branch; // @[cpu.scala 245:25]
  assign nextPCmod_io_jumptype = id_ex_ctrl_io_data_ex_ctrl_jumptype; // @[cpu.scala 246:25]
  assign nextPCmod_io_inputx = _T_12 ? id_ex_io_data_readdata1 : _T_16; // @[cpu.scala 270:23]
  assign nextPCmod_io_inputy = _T_17 ? id_ex_io_data_readdata2 : _T_21; // @[cpu.scala 271:23]
  assign nextPCmod_io_funct3 = id_ex_io_data_instruction[14:12]; // @[cpu.scala 274:23]
  assign nextPCmod_io_pc = id_ex_io_data_pc; // @[cpu.scala 272:23]
  assign nextPCmod_io_imm = id_ex_io_data_sextImm; // @[cpu.scala 273:23]
  assign pcPlusFour_io_inputx = pc; // @[cpu.scala 137:24]
  assign forwarding_io_rs1 = id_ex_io_data_instruction[19:15]; // @[cpu.scala 229:21]
  assign forwarding_io_rs2 = id_ex_io_data_instruction[24:20]; // @[cpu.scala 230:21]
  assign forwarding_io_exmemrd = ex_mem_io_data_instruction[11:7]; // @[cpu.scala 231:25]
  assign forwarding_io_exmemrw = ex_mem_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 232:25]
  assign forwarding_io_memwbrd = mem_wb_io_data_instruction[11:7]; // @[cpu.scala 233:25]
  assign forwarding_io_memwbrw = mem_wb_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 234:25]
  assign hazard_io_rs1 = if_id_io_data_instruction[19:15]; // @[cpu.scala 172:17]
  assign hazard_io_rs2 = if_id_io_data_instruction[24:20]; // @[cpu.scala 173:17]
  assign hazard_io_idex_memread = id_ex_ctrl_io_data_mem_ctrl_memop == 2'h2; // @[cpu.scala 224:26]
  assign hazard_io_idex_rd = id_ex_io_data_instruction[11:7]; // @[cpu.scala 226:26]
  assign hazard_io_exmem_taken = ex_mem_io_data_taken; // @[cpu.scala 320:25]
  assign if_id_clock = clock;
  assign if_id_reset = reset;
  assign if_id_io_in_instruction = potato1 ? io_imem_instruction[63:32] : io_imem_instruction[31:0]; // @[cpu.scala 148:29 cpu.scala 150:29]
  assign if_id_io_in_pc = pc; // @[cpu.scala 152:27]
  assign if_id_io_flush = hazard_io_if_id_flush; // @[cpu.scala 157:18]
  assign if_id_io_valid = ~hazard_io_if_id_stall; // @[cpu.scala 155:18]
  assign id_ex_clock = clock;
  assign id_ex_reset = reset;
  assign id_ex_io_in_pc = if_id_io_data_pc; // @[cpu.scala 184:27]
  assign id_ex_io_in_instruction = {{32'd0}, if_id_io_data_instruction}; // @[cpu.scala 185:27]
  assign id_ex_io_in_sextImm = immGen_io_sextImm; // @[cpu.scala 187:27]
  assign id_ex_io_in_readdata1 = registers_io_readdata1; // @[cpu.scala 188:27]
  assign id_ex_io_in_readdata2 = registers_io_readdata2; // @[cpu.scala 189:27]
  assign id_ex_io_flush = hazard_io_id_ex_flush; // @[cpu.scala 207:18]
  assign id_ex_ctrl_clock = clock;
  assign id_ex_ctrl_reset = reset;
  assign id_ex_ctrl_io_in_ex_ctrl_itype = control_io_itype; // @[cpu.scala 191:41]
  assign id_ex_ctrl_io_in_ex_ctrl_aluop = control_io_aluop; // @[cpu.scala 192:41]
  assign id_ex_ctrl_io_in_ex_ctrl_src1 = control_io_src1; // @[cpu.scala 193:41]
  assign id_ex_ctrl_io_in_ex_ctrl_src2 = control_io_src2; // @[cpu.scala 194:41]
  assign id_ex_ctrl_io_in_ex_ctrl_branch = control_io_branch; // @[cpu.scala 195:41]
  assign id_ex_ctrl_io_in_ex_ctrl_jumptype = control_io_jumptype; // @[cpu.scala 196:41]
  assign id_ex_ctrl_io_in_ex_ctrl_resultselect = control_io_resultselect; // @[cpu.scala 197:41]
  assign id_ex_ctrl_io_in_ex_ctrl_wordinst = control_io_wordinst; // @[cpu.scala 198:41]
  assign id_ex_ctrl_io_in_mem_ctrl_memop = control_io_memop; // @[cpu.scala 200:35]
  assign id_ex_ctrl_io_in_wb_ctrl_toreg = control_io_toreg; // @[cpu.scala 202:37]
  assign id_ex_ctrl_io_in_wb_ctrl_regwrite = control_io_regwrite; // @[cpu.scala 203:37]
  assign id_ex_ctrl_io_flush = hazard_io_id_ex_flush; // @[cpu.scala 210:23]
  assign ex_mem_clock = clock;
  assign ex_mem_reset = reset;
  assign ex_mem_io_in_ex_result = id_ex_ctrl_io_data_ex_ctrl_resultselect ? id_ex_io_data_sextImm : alu_io_result; // @[cpu.scala 289:26]
  assign ex_mem_io_in_mem_writedata = _T_17 ? id_ex_io_data_readdata2 : _T_21; // @[cpu.scala 278:30]
  assign ex_mem_io_in_nextpc = nextPCmod_io_nextpc; // @[cpu.scala 285:23]
  assign ex_mem_io_in_taken = nextPCmod_io_taken; // @[cpu.scala 286:23]
  assign ex_mem_io_in_instruction = id_ex_io_data_instruction; // @[cpu.scala 277:30]
  assign ex_mem_io_flush = hazard_io_ex_mem_flush; // @[cpu.scala 294:24]
  assign ex_mem_ctrl_clock = clock;
  assign ex_mem_ctrl_reset = reset;
  assign ex_mem_ctrl_io_in_mem_ctrl_memop = id_ex_ctrl_io_data_mem_ctrl_memop; // @[cpu.scala 281:38]
  assign ex_mem_ctrl_io_in_wb_ctrl_toreg = id_ex_ctrl_io_data_wb_ctrl_toreg; // @[cpu.scala 282:38]
  assign ex_mem_ctrl_io_in_wb_ctrl_regwrite = id_ex_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 283:38]
  assign ex_mem_ctrl_io_flush = hazard_io_ex_mem_flush; // @[cpu.scala 297:24]
  assign mem_wb_clock = clock;
  assign mem_wb_reset = reset;
  assign mem_wb_io_in_readdata = io_dmem_readdata; // @[cpu.scala 324:28]
  assign mem_wb_io_in_ex_result = ex_mem_io_data_ex_result; // @[cpu.scala 325:28]
  assign mem_wb_io_in_instruction = ex_mem_io_data_instruction; // @[cpu.scala 326:28]
  assign mem_wb_ctrl_clock = clock;
  assign mem_wb_ctrl_reset = reset;
  assign mem_wb_ctrl_io_in_wb_ctrl_toreg = ex_mem_ctrl_io_data_wb_ctrl_toreg; // @[cpu.scala 328:35]
  assign mem_wb_ctrl_io_in_wb_ctrl_regwrite = ex_mem_ctrl_io_data_wb_ctrl_regwrite; // @[cpu.scala 329:38]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  `ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {2{`RANDOM}};
  pc = _RAND_0[63:0];
  `endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if (reset) begin
      pc <= 64'h0;
    end else if (hazard_io_pcfromtaken) begin
      pc <= next_pc;
    end else if (!(hazard_io_pcstall)) begin
      pc <= pcPlusFour_io_result;
    end
  end
endmodule
module DualPortedCombinMemory(
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
  reg [31:0] memory [0:63]; // @[base-memory-components.scala 40:19]
  reg [31:0] _RAND_0;
  wire [31:0] memory__T_12_data; // @[base-memory-components.scala 40:19]
  wire [5:0] memory__T_12_addr; // @[base-memory-components.scala 40:19]
  wire [31:0] memory__T_14_data; // @[base-memory-components.scala 40:19]
  wire [5:0] memory__T_14_addr; // @[base-memory-components.scala 40:19]
  wire [31:0] memory__T_28_data; // @[base-memory-components.scala 40:19]
  wire [5:0] memory__T_28_addr; // @[base-memory-components.scala 40:19]
  wire [31:0] memory__T_30_data; // @[base-memory-components.scala 40:19]
  wire [5:0] memory__T_30_addr; // @[base-memory-components.scala 40:19]
  wire [31:0] memory__T_35_data; // @[base-memory-components.scala 40:19]
  wire [5:0] memory__T_35_addr; // @[base-memory-components.scala 40:19]
  wire  memory__T_35_mask; // @[base-memory-components.scala 40:19]
  wire  memory__T_35_en; // @[base-memory-components.scala 40:19]
  wire [31:0] memory__T_41_data; // @[base-memory-components.scala 40:19]
  wire [5:0] memory__T_41_addr; // @[base-memory-components.scala 40:19]
  wire  memory__T_41_mask; // @[base-memory-components.scala 40:19]
  wire  memory__T_41_en; // @[base-memory-components.scala 40:19]
  wire  _T_6 = io_imem_request_bits_address < 64'h100; // @[memory.scala 38:27]
  wire [63:0] _T_7 = {{3'd0}, io_imem_request_bits_address[63:3]}; // @[memory.scala 40:42]
  wire [64:0] _T_8 = {_T_7, 1'h0}; // @[memory.scala 40:50]
  wire [64:0] _T_10 = _T_8 + 65'h1; // @[memory.scala 41:60]
  wire [63:0] _T_15 = {memory__T_12_data,memory__T_14_data}; // @[Cat.scala 30:58]
  wire [63:0] _GEN_4 = _T_6 ? _T_15 : 64'h0; // @[memory.scala 38:37]
  wire  _T_16 = io_dmem_request_bits_operation != 2'h1; // @[memory.scala 60:31]
  wire  _T_18 = _T_16 | reset; // @[memory.scala 60:12]
  wire  _T_19 = ~_T_18; // @[memory.scala 60:12]
  wire  _T_20 = io_dmem_request_bits_address < 64'h100; // @[memory.scala 62:29]
  wire  _T_22 = _T_20 | reset; // @[memory.scala 62:12]
  wire  _T_23 = ~_T_22; // @[memory.scala 62:12]
  wire [63:0] _T_24 = {{2'd0}, io_dmem_request_bits_address[63:2]}; // @[memory.scala 65:34]
  wire [63:0] _T_26 = _T_24 + 64'h1; // @[memory.scala 66:58]
  wire [63:0] _T_31 = {memory__T_28_data,memory__T_30_data}; // @[Cat.scala 30:58]
  wire  _T_32 = io_dmem_request_bits_operation == 2'h2; // @[memory.scala 70:29]
  wire [61:0] _T_39 = io_dmem_request_bits_address[63:2] + 62'h1; // @[memory.scala 72:32]
  assign memory__T_12_addr = _T_10[5:0];
  assign memory__T_12_data = memory[memory__T_12_addr]; // @[base-memory-components.scala 40:19]
  assign memory__T_14_addr = _T_8[5:0];
  assign memory__T_14_data = memory[memory__T_14_addr]; // @[base-memory-components.scala 40:19]
  assign memory__T_28_addr = _T_26[5:0];
  assign memory__T_28_data = memory[memory__T_28_addr]; // @[base-memory-components.scala 40:19]
  assign memory__T_30_addr = _T_24[5:0];
  assign memory__T_30_data = memory[memory__T_30_addr]; // @[base-memory-components.scala 40:19]
  assign memory__T_35_data = io_dmem_request_bits_writedata[31:0];
  assign memory__T_35_addr = io_dmem_request_bits_address[7:2];
  assign memory__T_35_mask = 1'h1;
  assign memory__T_35_en = io_dmem_request_valid & _T_32;
  assign memory__T_41_data = io_dmem_request_bits_writedata[63:32];
  assign memory__T_41_addr = _T_39[5:0];
  assign memory__T_41_mask = 1'h1;
  assign memory__T_41_en = io_dmem_request_valid & _T_32;
  assign io_imem_response_bits_data = io_imem_request_valid ? _GEN_4 : 64'h0; // @[base-memory-components.scala 37:20 memory.scala 41:34]
  assign io_dmem_response_valid = io_dmem_request_valid; // @[base-memory-components.scala 38:20 memory.scala 19:27 memory.scala 67:28 memory.scala 75:28]
  assign io_dmem_response_bits_data = io_dmem_request_valid ? _T_31 : 64'h0; // @[base-memory-components.scala 38:20 memory.scala 66:32]
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
  _RAND_0 = {1{`RANDOM}};
  `ifdef RANDOMIZE_MEM_INIT
  for (initvar = 0; initvar < 64; initvar = initvar+1)
    memory[initvar] = _RAND_0[31:0];
  `endif // RANDOMIZE_MEM_INIT
  `endif // RANDOMIZE
end // initial
`endif // SYNTHESIS
  always @(posedge clock) begin
    if(memory__T_35_en & memory__T_35_mask) begin
      memory[memory__T_35_addr] <= memory__T_35_data; // @[base-memory-components.scala 40:19]
    end
    if(memory__T_41_en & memory__T_41_mask) begin
      memory[memory__T_41_addr] <= memory__T_41_data; // @[base-memory-components.scala 40:19]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (io_dmem_request_valid & _T_19) begin
          $fwrite(32'h80000002,"Assertion failed\n    at memory.scala:60 assert (request.operation =/= Write)\n"); // @[memory.scala 60:12]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (io_dmem_request_valid & _T_19) begin
          $fatal; // @[memory.scala 60:12]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (io_dmem_request_valid & _T_23) begin
          $fwrite(32'h80000002,"Assertion failed\n    at memory.scala:62 assert (request.address < size.U)\n"); // @[memory.scala 62:12]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (io_dmem_request_valid & _T_23) begin
          $fatal; // @[memory.scala 62:12]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
  end
endmodule
module ICombinMemPort(
  input  [63:0] io_pipeline_address,
  input         io_pipeline_valid,
  output [63:0] io_pipeline_instruction,
  output        io_bus_request_valid,
  output [63:0] io_bus_request_bits_address,
  input  [63:0] io_bus_response_bits_data
);
  assign io_pipeline_instruction = io_bus_response_bits_data; // @[base-memory-components.scala 53:15 memory-combin-ports.scala 34:27]
  assign io_bus_request_valid = io_pipeline_valid; // @[memory-combin-ports.scala 24:26 memory-combin-ports.scala 26:26]
  assign io_bus_request_bits_address = io_pipeline_address; // @[memory-combin-ports.scala 23:26]
endmodule
module DCombinMemPort(
  input         clock,
  input         reset,
  input  [63:0] io_pipeline_address,
  input         io_pipeline_valid,
  input  [63:0] io_pipeline_writedata,
  input         io_pipeline_memread,
  input         io_pipeline_memwrite,
  input  [1:0]  io_pipeline_maskmode,
  input         io_pipeline_sext,
  output [63:0] io_pipeline_readdata,
  output        io_bus_request_valid,
  output [63:0] io_bus_request_bits_address,
  output [63:0] io_bus_request_bits_writedata,
  output [1:0]  io_bus_request_bits_operation,
  input         io_bus_response_valid,
  input  [63:0] io_bus_response_bits_data
);
  wire  _T_1 = io_pipeline_memread | io_pipeline_memwrite; // @[memory-combin-ports.scala 45:51]
  wire  _T_2 = io_pipeline_valid & _T_1; // @[memory-combin-ports.scala 45:27]
  wire  _T_3 = io_pipeline_memread & io_pipeline_memwrite; // @[memory-combin-ports.scala 47:34]
  wire  _T_4 = ~_T_3; // @[memory-combin-ports.scala 47:12]
  wire  _T_6 = _T_4 | reset; // @[memory-combin-ports.scala 47:11]
  wire  _T_7 = ~_T_6; // @[memory-combin-ports.scala 47:11]
  wire  _T_9 = io_pipeline_maskmode != 2'h3; // @[memory-combin-ports.scala 78:34]
  wire  _T_16 = io_pipeline_maskmode == 2'h0; // @[memory-combin-ports.scala 89:36]
  wire  _T_20 = io_pipeline_maskmode == 2'h1; // @[memory-combin-ports.scala 91:43]
  wire  _T_24 = io_pipeline_maskmode == 2'h2; // @[memory-combin-ports.scala 93:43]
  wire [63:0] _GEN_4 = _T_24 ? 64'hffffffff : 64'hffffffffffffffff; // @[memory-combin-ports.scala 93:52]
  wire [63:0] _GEN_5 = _T_20 ? 64'hffff : _GEN_4; // @[memory-combin-ports.scala 91:52]
  wire [63:0] _GEN_6 = _T_16 ? 64'hff : _GEN_5; // @[memory-combin-ports.scala 89:45]
  wire [3:0] _GEN_20 = {{2'd0}, io_pipeline_address[1:0]}; // @[memory-combin-ports.scala 99:61]
  wire [5:0] _T_29 = _GEN_20 * 4'h8; // @[memory-combin-ports.scala 99:61]
  wire [126:0] _GEN_21 = {{63'd0}, _GEN_6}; // @[memory-combin-ports.scala 99:50]
  wire [126:0] _T_30 = _GEN_21 << _T_29; // @[memory-combin-ports.scala 99:50]
  wire [126:0] _GEN_23 = {{63'd0}, io_pipeline_writedata}; // @[memory-combin-ports.scala 100:52]
  wire [126:0] _T_32 = _GEN_23 << _T_29; // @[memory-combin-ports.scala 100:52]
  wire [63:0] _T_33 = ~_T_30[63:0]; // @[memory-combin-ports.scala 103:26]
  wire [63:0] _T_34 = io_bus_response_bits_data & _T_33; // @[memory-combin-ports.scala 105:32]
  wire [63:0] _T_35 = _T_32[63:0] & _T_30[63:0]; // @[memory-combin-ports.scala 105:70]
  wire [63:0] _T_36 = _T_34 | _T_35; // @[memory-combin-ports.scala 105:49]
  wire [63:0] _T_42 = io_bus_response_bits_data >> _T_29; // @[memory-combin-ports.scala 119:53]
  wire [63:0] _T_43 = _T_42 & 64'hff; // @[memory-combin-ports.scala 119:72]
  wire [63:0] _T_47 = _T_42 & 64'hffff; // @[memory-combin-ports.scala 122:72]
  wire [63:0] _T_51 = _T_42 & 64'hffffffff; // @[memory-combin-ports.scala 125:72]
  wire [63:0] _GEN_8 = _T_24 ? _T_51 : io_bus_response_bits_data; // @[memory-combin-ports.scala 123:50]
  wire [63:0] _GEN_9 = _T_20 ? _T_47 : _GEN_8; // @[memory-combin-ports.scala 120:50]
  wire [63:0] _GEN_10 = _T_16 ? _T_43 : _GEN_9; // @[memory-combin-ports.scala 117:43]
  wire [55:0] _T_55 = _GEN_10[7] ? 56'hffffffffffffff : 56'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_57 = {_T_55,_GEN_10[7:0]}; // @[Cat.scala 30:58]
  wire [47:0] _T_61 = _GEN_10[15] ? 48'hffffffffffff : 48'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_63 = {_T_61,_GEN_10[15:0]}; // @[Cat.scala 30:58]
  wire [31:0] _T_67 = _GEN_10[31] ? 32'hffffffff : 32'h0; // @[Bitwise.scala 72:12]
  wire [63:0] _T_69 = {_T_67,_GEN_10[31:0]}; // @[Cat.scala 30:58]
  wire [63:0] _GEN_11 = _T_24 ? _T_69 : _GEN_10; // @[memory-combin-ports.scala 138:52]
  wire [63:0] _GEN_12 = _T_20 ? _T_63 : _GEN_11; // @[memory-combin-ports.scala 135:52]
  wire [63:0] _GEN_13 = _T_16 ? _T_57 : _GEN_12; // @[memory-combin-ports.scala 132:45]
  wire [63:0] _GEN_14 = io_pipeline_sext ? _GEN_13 : _GEN_10; // @[memory-combin-ports.scala 131:31]
  wire [63:0] _T_38 = _GEN_14; // @[memory-combin-ports.scala 114:36 memory-combin-ports.scala 134:30 memory-combin-ports.scala 137:30 memory-combin-ports.scala 140:30 memory-combin-ports.scala 143:30 memory-combin-ports.scala 146:28]
  wire [63:0] _GEN_15 = io_pipeline_memread ? _T_38 : 64'h0; // @[memory-combin-ports.scala 111:39]
  wire [63:0] _GEN_17 = io_pipeline_memwrite ? 64'h0 : _GEN_15; // @[memory-combin-ports.scala 73:33]
  assign io_pipeline_readdata = io_bus_response_valid ? _GEN_17 : 64'h0; // @[base-memory-components.scala 70:15 memory-combin-ports.scala 149:28]
  assign io_bus_request_valid = io_pipeline_valid & _T_1; // @[memory-combin-ports.scala 50:26 memory-combin-ports.scala 68:26]
  assign io_bus_request_bits_address = io_pipeline_address; // @[memory-combin-ports.scala 49:33]
  assign io_bus_request_bits_writedata = _T_9 ? _T_36 : io_pipeline_writedata; // @[memory-combin-ports.scala 109:37]
  assign io_bus_request_bits_operation = io_pipeline_memwrite ? 2'h2 : 2'h0; // @[memory-combin-ports.scala 61:37 memory-combin-ports.scala 64:37]
  always @(posedge clock) begin
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_2 & _T_7) begin
          $fwrite(32'h80000002,"Assertion failed\n    at memory-combin-ports.scala:47 assert(!(io.pipeline.memread && io.pipeline.memwrite))\n"); // @[memory-combin-ports.scala 47:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (_T_2 & _T_7) begin
          $fatal; // @[memory-combin-ports.scala 47:11]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
  end
endmodule
module Top(
  input   clock,
  input   reset,
  output  io_success
);
  wire  cpu_clock; // @[top.scala 14:20]
  wire  cpu_reset; // @[top.scala 14:20]
  wire [63:0] cpu_io_imem_address; // @[top.scala 14:20]
  wire  cpu_io_imem_valid; // @[top.scala 14:20]
  wire  cpu_io_imem_good; // @[top.scala 14:20]
  wire [63:0] cpu_io_imem_instruction; // @[top.scala 14:20]
  wire  cpu_io_imem_ready; // @[top.scala 14:20]
  wire [63:0] cpu_io_dmem_address; // @[top.scala 14:20]
  wire  cpu_io_dmem_valid; // @[top.scala 14:20]
  wire  cpu_io_dmem_good; // @[top.scala 14:20]
  wire [63:0] cpu_io_dmem_writedata; // @[top.scala 14:20]
  wire  cpu_io_dmem_memread; // @[top.scala 14:20]
  wire  cpu_io_dmem_memwrite; // @[top.scala 14:20]
  wire [1:0] cpu_io_dmem_maskmode; // @[top.scala 14:20]
  wire  cpu_io_dmem_sext; // @[top.scala 14:20]
  wire [63:0] cpu_io_dmem_readdata; // @[top.scala 14:20]
  wire  mem_clock; // @[top.scala 15:20]
  wire  mem_reset; // @[top.scala 15:20]
  wire  mem_io_imem_request_valid; // @[top.scala 15:20]
  wire [63:0] mem_io_imem_request_bits_address; // @[top.scala 15:20]
  wire [63:0] mem_io_imem_response_bits_data; // @[top.scala 15:20]
  wire  mem_io_dmem_request_valid; // @[top.scala 15:20]
  wire [63:0] mem_io_dmem_request_bits_address; // @[top.scala 15:20]
  wire [63:0] mem_io_dmem_request_bits_writedata; // @[top.scala 15:20]
  wire [1:0] mem_io_dmem_request_bits_operation; // @[top.scala 15:20]
  wire  mem_io_dmem_response_valid; // @[top.scala 15:20]
  wire [63:0] mem_io_dmem_response_bits_data; // @[top.scala 15:20]
  wire [63:0] imem_io_pipeline_address; // @[top.scala 17:20]
  wire  imem_io_pipeline_valid; // @[top.scala 17:20]
  wire [63:0] imem_io_pipeline_instruction; // @[top.scala 17:20]
  wire  imem_io_bus_request_valid; // @[top.scala 17:20]
  wire [63:0] imem_io_bus_request_bits_address; // @[top.scala 17:20]
  wire [63:0] imem_io_bus_response_bits_data; // @[top.scala 17:20]
  wire  dmem_clock; // @[top.scala 18:20]
  wire  dmem_reset; // @[top.scala 18:20]
  wire [63:0] dmem_io_pipeline_address; // @[top.scala 18:20]
  wire  dmem_io_pipeline_valid; // @[top.scala 18:20]
  wire [63:0] dmem_io_pipeline_writedata; // @[top.scala 18:20]
  wire  dmem_io_pipeline_memread; // @[top.scala 18:20]
  wire  dmem_io_pipeline_memwrite; // @[top.scala 18:20]
  wire [1:0] dmem_io_pipeline_maskmode; // @[top.scala 18:20]
  wire  dmem_io_pipeline_sext; // @[top.scala 18:20]
  wire [63:0] dmem_io_pipeline_readdata; // @[top.scala 18:20]
  wire  dmem_io_bus_request_valid; // @[top.scala 18:20]
  wire [63:0] dmem_io_bus_request_bits_address; // @[top.scala 18:20]
  wire [63:0] dmem_io_bus_request_bits_writedata; // @[top.scala 18:20]
  wire [1:0] dmem_io_bus_request_bits_operation; // @[top.scala 18:20]
  wire  dmem_io_bus_response_valid; // @[top.scala 18:20]
  wire [63:0] dmem_io_bus_response_bits_data; // @[top.scala 18:20]
  PipelinedCPU cpu ( // @[top.scala 14:20]
    .clock(cpu_clock),
    .reset(cpu_reset),
    .io_imem_address(cpu_io_imem_address),
    .io_imem_valid(cpu_io_imem_valid),
    .io_imem_good(cpu_io_imem_good),
    .io_imem_instruction(cpu_io_imem_instruction),
    .io_imem_ready(cpu_io_imem_ready),
    .io_dmem_address(cpu_io_dmem_address),
    .io_dmem_valid(cpu_io_dmem_valid),
    .io_dmem_good(cpu_io_dmem_good),
    .io_dmem_writedata(cpu_io_dmem_writedata),
    .io_dmem_memread(cpu_io_dmem_memread),
    .io_dmem_memwrite(cpu_io_dmem_memwrite),
    .io_dmem_maskmode(cpu_io_dmem_maskmode),
    .io_dmem_sext(cpu_io_dmem_sext),
    .io_dmem_readdata(cpu_io_dmem_readdata)
  );
  DualPortedCombinMemory mem ( // @[top.scala 15:20]
    .clock(mem_clock),
    .reset(mem_reset),
    .io_imem_request_valid(mem_io_imem_request_valid),
    .io_imem_request_bits_address(mem_io_imem_request_bits_address),
    .io_imem_response_bits_data(mem_io_imem_response_bits_data),
    .io_dmem_request_valid(mem_io_dmem_request_valid),
    .io_dmem_request_bits_address(mem_io_dmem_request_bits_address),
    .io_dmem_request_bits_writedata(mem_io_dmem_request_bits_writedata),
    .io_dmem_request_bits_operation(mem_io_dmem_request_bits_operation),
    .io_dmem_response_valid(mem_io_dmem_response_valid),
    .io_dmem_response_bits_data(mem_io_dmem_response_bits_data)
  );
  ICombinMemPort imem ( // @[top.scala 17:20]
    .io_pipeline_address(imem_io_pipeline_address),
    .io_pipeline_valid(imem_io_pipeline_valid),
    .io_pipeline_instruction(imem_io_pipeline_instruction),
    .io_bus_request_valid(imem_io_bus_request_valid),
    .io_bus_request_bits_address(imem_io_bus_request_bits_address),
    .io_bus_response_bits_data(imem_io_bus_response_bits_data)
  );
  DCombinMemPort dmem ( // @[top.scala 18:20]
    .clock(dmem_clock),
    .reset(dmem_reset),
    .io_pipeline_address(dmem_io_pipeline_address),
    .io_pipeline_valid(dmem_io_pipeline_valid),
    .io_pipeline_writedata(dmem_io_pipeline_writedata),
    .io_pipeline_memread(dmem_io_pipeline_memread),
    .io_pipeline_memwrite(dmem_io_pipeline_memwrite),
    .io_pipeline_maskmode(dmem_io_pipeline_maskmode),
    .io_pipeline_sext(dmem_io_pipeline_sext),
    .io_pipeline_readdata(dmem_io_pipeline_readdata),
    .io_bus_request_valid(dmem_io_bus_request_valid),
    .io_bus_request_bits_address(dmem_io_bus_request_bits_address),
    .io_bus_request_bits_writedata(dmem_io_bus_request_bits_writedata),
    .io_bus_request_bits_operation(dmem_io_bus_request_bits_operation),
    .io_bus_response_valid(dmem_io_bus_response_valid),
    .io_bus_response_bits_data(dmem_io_bus_response_bits_data)
  );
  assign io_success = 1'h0;
  assign cpu_clock = clock;
  assign cpu_reset = reset;
  assign cpu_io_imem_good = 1'h1; // @[top.scala 23:15]
  assign cpu_io_imem_instruction = imem_io_pipeline_instruction; // @[top.scala 23:15]
  assign cpu_io_imem_ready = 1'h1; // @[top.scala 23:15]
  assign cpu_io_dmem_good = 1'h1; // @[top.scala 24:15]
  assign cpu_io_dmem_readdata = dmem_io_pipeline_readdata; // @[top.scala 24:15]
  assign mem_clock = clock;
  assign mem_reset = reset;
  assign mem_io_imem_request_valid = imem_io_bus_request_valid; // @[base-memory-components.scala 17:26]
  assign mem_io_imem_request_bits_address = imem_io_bus_request_bits_address; // @[base-memory-components.scala 17:26]
  assign mem_io_dmem_request_valid = dmem_io_bus_request_valid; // @[base-memory-components.scala 20:26]
  assign mem_io_dmem_request_bits_address = dmem_io_bus_request_bits_address; // @[base-memory-components.scala 20:26]
  assign mem_io_dmem_request_bits_writedata = dmem_io_bus_request_bits_writedata; // @[base-memory-components.scala 20:26]
  assign mem_io_dmem_request_bits_operation = dmem_io_bus_request_bits_operation; // @[base-memory-components.scala 20:26]
  assign imem_io_pipeline_address = cpu_io_imem_address; // @[top.scala 23:15]
  assign imem_io_pipeline_valid = cpu_io_imem_valid; // @[top.scala 23:15]
  assign imem_io_bus_response_bits_data = mem_io_imem_response_bits_data; // @[base-memory-components.scala 18:26]
  assign dmem_clock = clock;
  assign dmem_reset = reset;
  assign dmem_io_pipeline_address = cpu_io_dmem_address; // @[top.scala 24:15]
  assign dmem_io_pipeline_valid = cpu_io_dmem_valid; // @[top.scala 24:15]
  assign dmem_io_pipeline_writedata = cpu_io_dmem_writedata; // @[top.scala 24:15]
  assign dmem_io_pipeline_memread = cpu_io_dmem_memread; // @[top.scala 24:15]
  assign dmem_io_pipeline_memwrite = cpu_io_dmem_memwrite; // @[top.scala 24:15]
  assign dmem_io_pipeline_maskmode = cpu_io_dmem_maskmode; // @[top.scala 24:15]
  assign dmem_io_pipeline_sext = cpu_io_dmem_sext; // @[top.scala 24:15]
  assign dmem_io_bus_response_valid = mem_io_dmem_response_valid; // @[base-memory-components.scala 21:26]
  assign dmem_io_bus_response_bits_data = mem_io_dmem_response_bits_data; // @[base-memory-components.scala 21:26]
endmodule
