#!/usr/bin/env python3

import sys
import os
import unittest

from hagent.tool.compile_slang import Compile_slang


def inline_verilog():
    # Minimal Verilog code to be compiled.
    verilog_code = r"""
module trivial(input [2:0] a, input [2:0] b, output [1:0] c);
wire tmp;  // Warning, undriven
assign c = a ^ tmp; // warning here about conversion
assign x = a[1] ^ b[0] // error here -- Semicolon
endmodule

module leaf5(input [29:0] ci, output [29:0] co);
  assign co = ~ci;
endmodule
"""
    verilog_code2 = r"""
module leaf1(input [14:0] ai, output [14:0] ao);
  assign ao = (~ai == 15'h0) ? 15'h5 : 15'h0;
endmodule

module leaf2(input [14:0] ai, output [14:0] ao, input [24:0] bi, output [24:0] bo);
  // longer temp expression to get some variability in the area of the leaves
  assign ao = bi ^ ~{bi[15:0], bi[24:16]} / ai;
  assign bo = bi * 7;
endmodule

module leaf3(input [29:0] ci, output [29:0] co);
  assign co = ~ci;
endmodule

module leaf4(input[29:0] tempi, output[29:0] tempo);
  assign tempo = tempi - 2;
endmodule

module leaf5(input [29:0] ci, output [29:0] co);
  assign co = ~ci;
endmodule

module leaf6(input tempi, output tempo);
  assign tempo = ~tempi;
endmodule

module leaf7(input [24:0] bi, output [24:0] bo);
  assign bo = bi + bi;
endmodule

module leaf8(input [1:0] i, output [1:0] o);
  assign o = i * 2;
endmodule

module leafout(input oi, output oo);
  assign oo = ~oi;
endmodule

module mid1(input [59:0] di, output [59:0] dout);
  wire [14:0] w_1_to_2;
  wire [14:0] w_2_to_1;

  wire [24:0] w_2_to_7;
  wire [24:0] w_7_to_2;

  leaf1 l1(.ai(w_2_to_1), .ao(w_1_to_2));
  leaf1 ltest(.ai(w_2_to_1), .ao(dout[15:1]));
  leafout lout(.oi(1'b1), .oo(dout[0]));
  leaf2 l2(.ai(w_1_to_2), .ao(w_2_to_1), .bi(w_7_to_2), .bo(w_2_to_7));
  leaf7 l7(.bi(w_2_to_7), .bo(w_7_to_2));

  assign dout = ~{w_7_to_2[19:0], w_1_to_2, w_2_to_7};
endmodule

module mid2(input [59:0] di, output [59:0] dout, input [9:0] ei, output [9:0] eo);
  wire [29:0] w_3_to_5;
  wire [29:0] w_5_to_3;

  leaf3 l3(.ci(di[29:0]), .co(w_3_to_5));
  leaf4 l4(.tempi(w_3_to_5), .tempo(w_3_to_5));
  leaf5 l5(.ci(w_3_to_5), .co(w_5_to_3));

  assign dout = ~{di[59:30], w_3_to_5};
  assign eo = ~{ei[9:1], w_5_to_3[0]};
endmodule

module mid4(input [9:0] ei, output [9:0] eo, input [4:0] fi, output [4:0] fo);
  assign eo = ~ei;
  assign fo = ~fi;
endmodule

module mid3(input [4:0] fi, output [4:0] fo);
  wire w_o_6;
  leaf6 l6(.tempi(fi[3]), .tempo(w_o_6));
  assign fo = ~{fi[4:1], w_o_6};
endmodule

module mid5(input [59:0] gi, output [890:0] gout, input [9:0] hi, output [9:0] ho);
  wire [29:0] w_3_to_5;
  wire [29:0] w_5_to_3;

  wire [899:0] w_1_up_5;

  mid1 m1s(.di(gi), .dout(w_1_up_5));

  leaf3 l3d(.ci(gi[58:28]), .co(w_3_to_5));
  leaf4 l4d(.tempi(w_3_to_5[12]), .tempo(w_3_to_5[13]));
  leaf5 l5d(.ci(w_3_to_5), .co(w_5_to_3));

  assign gout = ~{gi[59:30] & w_1_up_5[890:30], w_3_to_5};
  assign ho = ~{hi[9:1], w_5_to_3[0]};
endmodule

module hier_test(input [59:0] testi, output [59:0] testo);
  wire [59:0] w_1_to_2;
  wire [59:0] w_2_to_1;

  wire [9:0] w_2_to_4;
  wire [9:0] w_4_to_2;

  wire [4:0] w_4_to_3;
  wire [4:0] w_3_to_4;

  wire [59:0] m5out;
  wire [59:0] m6out;

  mid1 m1(.di(w_2_to_1), .dout(w_1_to_2));
  mid2 m2(.di(w_1_to_2), .dout(w_2_to_1), .ei(w_2_to_4), .eo(w_4_to_2));
  mid3 m3(.fi(w_4_to_3), .fo(w_3_to_4));
  mid4 m4(.ei(w_4_to_2), .eo(w_2_to_4), .fi(w_3_to_4), .fo(w_4_to_3));

  // higher-level duplicate instantiation, for regularity discovery
  mid5 m5(.gi(w_1_to_2), .gout(m5out), .hi(w_2_to_4), .ho(m5out[9:0]));
  mid5 m6(.gi(w_1_to_2), .gout(m6out), .hi(w_2_to_4), .ho(m6out[9:0]));

  leaf8 l8(.i(testi[1:0]), .o(testo[1:0]));

  assign testo = ~{testi[0], w_2_to_1[49:2], m5out[1], m6out[0], w_2_to_4, w_3_to_4};

endmodule
"""

    # Create an instance of the Compile_slang tool.
    compiler = Compile_slang()

    # Validate setup: Ensure the pyslang package is present.
    if not compiler.setup():
        print('Setup failed:', compiler.error_message, file=sys.stderr)
        sys.exit(1)

    compiler.add_inline(verilog_code)

    if compiler.set_top('potato'):
        print('Potato should not be a valid top', file=sys.stderr)
        sys.exit(1)

    hierarchy = compiler.get_top_list()
    assert len(hierarchy) == 2
    sum('trivial' in s for s in hierarchy)
    sum('leaf5' in s for s in hierarchy)

    # Not needed to set trivial if there is a single module
    if not compiler.set_top('trivial'):
        print('Failed to set trivial as top module.', file=sys.stderr)
        sys.exit(1)

    hierarchy = compiler.get_top_list()
    assert len(hierarchy) == 1
    assert hierarchy[0] == 'trivial'

    # Retrieve input/output definitions from the top module.
    ios = compiler.get_ios()
    assert len(ios) == 3
    assert ios[0].name == 'a'
    assert ios[1].name == 'b'
    assert ios[2].name == 'c'

    assert ios[0].input == True
    assert ios[1].input == True
    assert ios[2].input == False

    assert ios[0].output == False
    assert ios[1].output == False
    assert ios[2].output == True

    assert ios[0].bits == 3
    assert ios[1].bits == 3
    assert ios[2].bits == 2

    # Retrieve compilation warnings and errors.
    warnings = compiler.get_warnings()
    errors = compiler.get_errors()
    assert len(warnings) > 2
    assert len(errors) == 1
    print(f'err:{errors[0].to_str()}')
    assert errors[0].loc > 0

    compiler2 = Compile_slang()
    compiler2.setup()  # clears the list of tops
    compiler2.add_inline(verilog_code2)
    hier2 = compiler2.get_top_list()
    assert len(hier2) == 1
    for a in hier2:
        print(f'hier:{a}')


def from_fileverilog(args):
    compiler = Compile_slang()

    use_command_line_args = False

    if use_command_line_args:
        compiler.setup(f'-f {args[0]}')
    else:
        compiler.setup()

        for a in args:
            ok = compiler.add_file(file=a)
            if not ok:
                print(f'OOPS {compiler.error_message}')

    hier = compiler.get_top_list()
    for a in hier:
        print(f'top level module options:{a}')

    err = compiler.get_errors()
    for a in err:
        print(f'ERR: File {a.file} Line {a.loc} msg:{a.msg}')

    err = compiler.get_warnings()
    for a in err:
        print(f'WARN: File {a.file} Line {a.loc} msg:{a.msg}')

from hagent.core.step import Step
from typing import Dict

# Trivial example of extending the Pass class
class Step_compile_slang(Step):
    def setup(self):
        super().setup()  # superclass

    def run(self, data: Dict):
        ret = data.copy()

        code = data.get('code',"")
        files = data.get('files',"")

        compiler = Compile_slang()

        if files:
            compiler.setup(f'-f {files}')
        else:
            compiler.setup()

        if code:
            ok = compiler.add_inline(text=code)
            if not ok:
                print(f'ERROR, could not compile {compiler.error_message}')
                sys.exit(3)

        hier = compiler.get_top_list()
        for a in hier:
            print(f'top level module options:{a}')

        err = compiler.get_errors()
        if err:
            err_list = []
            for a in err:
                print(f'ERR: File {a.file} Line {a.loc} msg:{a.msg}')
                err_list.append(a.to_str())

            if err_list:
                ret['err'] = err_list


        err = compiler.get_warnings()
        if err:
            err_list = []
            for a in err:
                print(f'WARN: File {a.file} Line {a.loc} msg:{a.msg}')
                err_list.append(a.to_str())

            if err_list:
                ret['warn'] = err_list

        return ret

def from_fileyaml(args):

    for arg in args:
        st = Step_compile_slang()
        filename = os.path.basename(arg)
        st.set_io(inp_file=arg, out_file=f"out_{filename}")

        st.setup()
        st.step()


def main(args):
    # Ensure args is a list
    assert isinstance(args, list), 'args must be a list'
    if len(args) == 0:
        return inline_verilog()
    elif len(args) == 1:
        filename = args[0]
        if filename.endswith(".yaml"):
            return from_fileyaml(args)
        else:
            return from_fileverilog(args)
    else:
        return from_fileverilog(args)


if __name__ == '__main__':
    # If first argument is "test", run the unit tests
    if len(sys.argv) > 1 and sys.argv[1] == 'test':
        # Remove the test argument to prevent unittest from misinterpreting it
        sys.argv.pop(1)
        unittest.main()
    else:
        # Call main with command-line arguments (excluding the script name)
        main(sys.argv[1:])
