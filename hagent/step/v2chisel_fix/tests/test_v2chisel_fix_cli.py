
import sys
import os

from hagent.step.v2chisel_fix.v2chisel_fix import V2chisel_fix



def process_chisel(files):

    step_obj = V2chisel_fix()

    inp_data = {}

    with open(files[0], "r") as fd:
        data = {}
        data['chisel_changed'] = fd.read()  # chisel_original
        data['was_valid'] = True
        inp_data['chisel_pass1'] = data

    with open(files[1], "r") as fd:
        data = {}
        data['verilog_candidate'] = fd.read()  # verilog_original
        inp_data['chisel_pass1'] = data

    with open(files[2], "r") as fd:
        inp_data['verilog_fixed'] = fd.read()

    step_obj.set_io(inp_file="", out_file = 'test_v2chisel_fix_cli.yaml', overwrite_conf = inp_data)

    step_obj.setup()

    res = step_obj.step()

    if "chisel_fix" in res:
        out_dict = res['chisel_fix']
        if "refined_chisel" in out_dict:
            print("Chisel fixed:")
            print(out_dict['refined_chisel'])


def main(args):
    if len(args) != 3:
        print("Call chisel_original.scala verilog_original.v verilog_fix.v")
    else:
        process_chisel(args)

if __name__ == "__main__":
    # If first argument is "test", run the unit tests
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        # Remove the test argument to prevent unittest from misinterpreting it
        sys.argv.pop(1)
        # unittest.main()
    else:
        # Call main with command-line arguments (excluding the script name)
        main(sys.argv[1:])
