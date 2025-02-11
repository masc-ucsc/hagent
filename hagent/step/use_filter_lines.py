# hagent/step/use_filter_lines.py

import argparse
import os
import sys
import tempfile
from hagent.tool.filter_lines import FilterLines

def main():
    parser = argparse.ArgumentParser(
        description="Filter Chisel source lines that best match a hard-coded Verilog diff."
    )
    parser.add_argument("chisel_file", help="Path to the Chisel source file")
    parser.add_argument("-c", "--context", type=int, default=0,
                        help="Number of context lines to include before and after each match (like grep -C)")
    args = parser.parse_args()

    if not os.path.isfile(args.chisel_file):
        print(f"Error: Chisel file '{args.chisel_file}' does not exist.", file=sys.stderr)
        sys.exit(1)

    # Hard-code the Verilog diff here (you can copy and paste your diff)
    verilog_diff = """--- verilog_original.v
+++ verilog_fixed.v
@@ -595,6 +595,6 @@
   assign io_funct3Out = io_instrOut_0[14:12];  // src/main/scala/SimpleRISCVCpu.scala:7:7, :50:28, :52:28
   assign io_rs1DataOut = io_rs1DataOut_0;      // src/main/scala/SimpleRISCVCpu.scala:7:7, :73:29
   assign io_rs2DataOut = io_rs2DataOut_0;      // src/main/scala/SimpleRISCVCpu.scala:7:7, :73:29
-  assign io_immOut = {{20{io_instrOut_0[31]}}, io_instrOut_0[31:20]};  // src/main/scala/SimpleRISCVCpu.scala:7:7, :50:28, :59:{19,24,40,58}
+  assign io_immOut = {{20{io_instrOut_0[31]}}, io_instrOut_0[28:20]};  // src/main/scala/SimpleRISCVCpu.scala:7:7, :50:28, :59:{19,24,40,58}
   assign io_branchTaken = branchTaken; // src/main/scala/SimpleRISCVCpu.scala:7:7, :73:29
 endmodule"""

    # Write the hard-coded diff to a temporary file so FilterLines can read it
    with tempfile.NamedTemporaryFile("w+", delete=False, suffix=".diff") as temp_diff:
        temp_diff.write(verilog_diff)
        temp_diff.flush()
        diff_file = temp_diff.name

    filter_tool = FilterLines()
    try:
        result = filter_tool.filter_lines(diff_file, args.chisel_file)
        print(result)
    except RuntimeError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    finally:
        os.remove(diff_file)

if __name__ == "__main__":
    main()
