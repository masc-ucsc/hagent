#!/usr/bin/env python3
"""
Simple LEC test that bypasses most of the pipeline and directly tests LEC.

This test creates known golden and gate files, then tests just the LEC functionality.
"""

import os
import sys
import tempfile
import subprocess

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))


def create_test_verilog_files(golden_dir, gate_dir):
    """Create test golden and gate Verilog files with known differences"""

    # Create Control.sv files with known difference
    golden_control_content = """module Control (
  input      [6:0] io_opcode,
  output           io_validinst,
  output           io_controltransferins,
  output           io_jump,
  output           io_branch,
  output           io_memread,
  output           io_memwrite,
  output           io_regwrite,
  output           io_memtoreg,
  output     [1:0] io_aluop,
  output           io_operand1_src,
  output           io_operand2_src,
  output           io_extend,
  output     [1:0] io_next_pc_sel
);
  wire _signals_T_132 = io_opcode == 7'h3B;  // Original value
  // ... rest of the module
  assign io_validinst = _signals_T_132;
  assign io_controltransferins = 1'h0;
  assign io_jump = 1'h0;
  assign io_branch = 1'h0;
  assign io_memread = 1'h0;
  assign io_memwrite = 1'h0;
  assign io_regwrite = 1'h1;
  assign io_memtoreg = 1'h0;
  assign io_aluop = 2'h1;
  assign io_operand1_src = 1'h0;
  assign io_operand2_src = 1'h0;
  assign io_extend = 1'h0;
  assign io_next_pc_sel = 2'h0;
endmodule"""

    gate_control_content = """module Control (
  input      [6:0] io_opcode,
  output           io_validinst,
  output           io_controltransferins,
  output           io_jump,
  output           io_branch,
  output           io_memread,
  output           io_memwrite,
  output           io_regwrite,
  output           io_memtoreg,
  output     [1:0] io_aluop,
  output           io_operand1_src,
  output           io_operand2_src,
  output           io_extend,
  output     [1:0] io_next_pc_sel
);
  wire _signals_T_132 = io_opcode == 7'h3F;  // Modified value
  // ... rest of the module
  assign io_validinst = _signals_T_132;
  assign io_controltransferins = 1'h0;
  assign io_jump = 1'h0;
  assign io_branch = 1'h0;
  assign io_memread = 1'h0;
  assign io_memwrite = 1'h0;
  assign io_regwrite = 1'h1;
  assign io_memtoreg = 1'h0;
  assign io_aluop = 2'h1;
  assign io_operand1_src = 1'h0;
  assign io_operand2_src = 1'h0;
  assign io_extend = 1'h0;
  assign io_next_pc_sel = 2'h0;
endmodule"""

    # Create SingleCycleCPU.sv files (should be identical for this test)
    cpu_content = """module SingleCycleCPU (
  input         io_clock,
  input         io_reset,
  input  [31:0] io_imem_instruction,
  input  [31:0] io_dmem_readdata,
  output [31:0] io_imem_address,
  output [31:0] io_dmem_address,
  output [31:0] io_dmem_writedata,
  output        io_dmem_memread,
  output        io_dmem_memwrite,
  output [3:0]  io_dmem_maskmode,
  output [1:0]  io_dmem_sext,
  output        io_dmem_valid
);
  // Simple CPU implementation for testing
  Control control_inst (
    .io_opcode(io_imem_instruction[6:0]),
    .io_validinst(),
    .io_controltransferins(),
    .io_jump(),
    .io_branch(),
    .io_memread(io_dmem_memread),
    .io_memwrite(io_dmem_memwrite),
    .io_regwrite(),
    .io_memtoreg(),
    .io_aluop(),
    .io_operand1_src(),
    .io_operand2_src(),
    .io_extend(),
    .io_next_pc_sel()
  );
  
  assign io_imem_address = 32'h0;
  assign io_dmem_address = 32'h0;
  assign io_dmem_writedata = 32'h0;
  assign io_dmem_maskmode = 4'h0;
  assign io_dmem_sext = 2'h0;
  assign io_dmem_valid = 1'h1;
endmodule"""

    # Write golden files
    os.makedirs(golden_dir, exist_ok=True)
    with open(os.path.join(golden_dir, 'Control.sv'), 'w') as f:
        f.write(golden_control_content)
    with open(os.path.join(golden_dir, 'SingleCycleCPU.sv'), 'w') as f:
        f.write(cpu_content)

    # Write gate files
    os.makedirs(gate_dir, exist_ok=True)
    with open(os.path.join(gate_dir, 'Control.sv'), 'w') as f:
        f.write(gate_control_content)
    with open(os.path.join(gate_dir, 'SingleCycleCPU.sv'), 'w') as f:
        f.write(cpu_content)

    return ['Control.sv', 'SingleCycleCPU.sv']


def test_lec_simple():
    """Test LEC with simple known files"""
    print('🧪 SIMPLE LEC TEST')
    print('=' * 50)
    print('Testing LEC with manually created golden and gate files')
    print("Expected: Control modules differ (7'h3B vs 7'h3F) but should be logically equivalent")
    print()

    with tempfile.TemporaryDirectory() as temp_dir:
        golden_dir = os.path.join(temp_dir, 'golden')
        gate_dir = os.path.join(temp_dir, 'gate')

        # Create test files
        print('📁 Creating test Verilog files...')
        files = create_test_verilog_files(golden_dir, gate_dir)
        print(f'✅ Created {len(files)} file pairs: {files}')

        # Build LEC command
        cli_equiv_check_path = '/home/farzaneh/hagent/hagent/tool/tests/cli_equiv_check.py'
        lec_cmd = ['uv', 'run', 'python', cli_equiv_check_path]

        # Add golden files
        for filename in files:
            golden_file = os.path.join(golden_dir, filename)
            lec_cmd.extend(['-r', golden_file])

        # Add gate files
        for filename in files:
            gate_file = os.path.join(gate_dir, filename)
            lec_cmd.extend(['-i', gate_file])

        # Add top module and verbose
        lec_cmd.extend(['--top', 'SingleCycleCPU', '--verbose'])

        print('🚀 Running LEC command:')
        print(f'     {" ".join(lec_cmd)}')
        print()

        # Execute LEC
        try:
            result = subprocess.run(lec_cmd, capture_output=True, text=True, timeout=300)

            print('📊 LEC RESULTS:')
            print(f'     Exit code: {result.returncode}')
            print()

            if result.stdout:
                print('📋 STDOUT:')
                print(result.stdout)
                print()

            if result.stderr:
                print('⚠️  STDERR:')
                print(result.stderr)
                print()

            # Analyze results
            if result.returncode == 0:
                print('✅ LEC TEST PASSED: Designs are equivalent!')
                return True
            elif result.returncode == 1:
                if 'NOT equivalent' in result.stdout:
                    print('❌ LEC TEST: Designs are NOT equivalent')
                    print('   This might be expected if the change affects logic')
                else:
                    print('❌ LEC TEST FAILED: Unknown equivalence issue')
                return False
            else:
                print(f'❌ LEC TEST FAILED: Unexpected exit code {result.returncode}')
                return False

        except subprocess.TimeoutExpired:
            print('❌ LEC TEST FAILED: Timeout (300s)')
            return False
        except Exception as e:
            print(f'❌ LEC TEST FAILED: Exception {e}')
            return False


def main():
    """Run the simple LEC test"""
    print('🔬 SIMPLE LEC ISOLATION TEST')
    print('=' * 60)
    print('Purpose: Test LEC tool directly with known test files')
    print('This bypasses the entire v2chisel_batch pipeline')
    print('=' * 60)
    print()

    success = test_lec_simple()

    print()
    print('=' * 60)
    if success:
        print('🎉 TEST RESULT: LEC tool works correctly!')
        sys.exit(0)
    else:
        print('💥 TEST RESULT: LEC tool has issues')
        sys.exit(1)


if __name__ == '__main__':
    main()
