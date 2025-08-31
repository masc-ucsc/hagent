#!/usr/bin/env python3
# See LICENSE for details

import os
import sys
import subprocess
from hagent.core.step import Step
from hagent.tool.equiv_check import Equiv_check
from hagent.tool.extract_code import Extract_code_verilog


class Select_best(Step):
    def setup(self):
        super().setup()  # superclass
        print(f'input_file:{self.input_file}')

        self.verilog_extractor = Extract_code_verilog()

        self.setup_called = True

        eq_checker = Equiv_check()
        if not eq_checker.setup():
            err = eq_checker.get_error() or 'Yosys not found'
            print(f'[ERROR] Equiv_check setup failed: {err}')
            sys.exit(1)

    def _synthesize_module(self, code, mod_name, work_dir, liberty_file):
        """
        Synthesize the given Verilog module using Yosys and generate the netlist.
        Returns the netlist file path.
        """
        # Create intermediate Verilog file
        verilog_file = os.path.join(work_dir, f'{mod_name}_temp.v')
        with open(verilog_file, 'w') as f:
            f.write(code)

        # Synthesize using Yosys to generate the netlist with liberty file
        netlist_file = os.path.join(work_dir, f'{mod_name}_netlist_temp.v')
        yosys_script = f"""
        read_verilog -sv -defer {verilog_file}
        hierarchy -top {mod_name};
        flatten {mod_name};
        opt;
        synth -top {mod_name};
        dfflibmap -liberty {liberty_file};
        printattrs;
        stat;
        abc -liberty {liberty_file} -dff -keepff -g aig;
        write_verilog {netlist_file}
        """
        yosys_cmd = ['yosys', '-p', yosys_script]

        try:
            subprocess.run(yosys_cmd, check=True)
        except subprocess.CalledProcessError:
            print(f'Error synthesizing {mod_name} with Yosys')
            return None

        return netlist_file

    def _update_best_version(self, best_time, current_time, result, code):
        """Update the best version if the current arrival time is smaller."""
        if current_time < best_time:
            result['best_version'] = code
            return current_time
        return best_time

    def _analyze_timing(self, netlist_file, mod_name, work_dir, liberty_file):
        """
        Analyze timing using OpenSTA and generate a timing report.
        Returns the arrival time extracted from the report.
        """
        timing_report = os.path.join(work_dir, f'{mod_name}_timing.rpt')
        sta_tcl = os.path.join(work_dir, f'{mod_name}_sta.tcl')

        # Generate OpenSTA TCL script
        with open(sta_tcl, 'w') as f:
            f.write(f"""
            read_liberty {liberty_file}
            set_units -time ns -capacitance pF -voltage V -current mA -resistance kOhm -distance um
            set_operating_conditions ff_100C_1v95
            read_verilog {netlist_file}
            link_design {mod_name}
            create_clock -name virtual_clock -period 10 [get_ports clock]
            set_output_delay 0 -clock virtual_clock [all_outputs]
            report_checks -path_delay max > {timing_report}
            exit
            """)

        # Run OpenSTA with the generated TCL script
        opensta_cmd = [os.path.expanduser('~/opensta/OpenSTA/app/sta'), sta_tcl]

        try:
            subprocess.run(opensta_cmd, check=True)
        except subprocess.CalledProcessError:
            print(f'Error analyzing timing for {mod_name} with OpenSTA')
            return float('inf')

        return self._extract_arrival_time(timing_report)

    def _extract_arrival_time(self, report_path):
        """Extract the smallest arrival time from the timing report."""
        try:
            with open(report_path, 'r') as file:
                for line in file:
                    if 'data arrival time' in line.lower():
                        # Extract the first number (arrival time) from the line
                        parts = line.split()
                        for part in parts:
                            try:
                                arrival_time = float(part)
                                print(f'----\n ARRIVAL TIME: {arrival_time}  \n -----')
                                return arrival_time
                            except ValueError:
                                continue
        except Exception as e:
            print(f'Error reading timing report: {e}')
        return float('inf')  # Return a large delay if parsing fails

    def run(self, data):
        """
        1. Read data (contents of optimized_equivalent) from output yaml of replicate_code.py
        2. Synthesize each verilog in optimized_equivalent, and find its max frequency.
        3. The definition with best or max freq is to be selected and stored in the same directory.
        4. output file should be named as: best_version_<mod_name>.v
        """
        mod_name = os.path.splitext(os.path.basename(self.input_file))[0]  # get module name from yaml file name
        codes = data['optimized_equivalent']
        print(f'----mod_name:{mod_name}-----has {len(codes)} equivalent codes -----')
        work_dir = os.path.dirname(self.input_file)  # Use the directory of the input YAML file for intermediate files
        best_time = float('inf')

        result = {'best_version': None}

        for code in codes:
            parsed_codes = self.verilog_extractor.parse(code)
            if not parsed_codes or not parsed_codes[0]:
                continue
            code = parsed_codes[0]
            netlist_file = self._synthesize_module(code, mod_name, work_dir, 'sky130_fd_sc_hd__ff_100C_1v95.lib')
            if netlist_file:
                arrival_time = self._analyze_timing(netlist_file, mod_name, work_dir, 'sky130_fd_sc_hd__ff_100C_1v95.lib')
                best_time = self._update_best_version(best_time, arrival_time, result, code)

        print(f'Best version found with arrival time: {best_time:.2f}')

        ##         os.makedirs(os.path.dirname(filename), exist_ok=True)
        ##         with open(filename, 'w') as f:
        ##             f.write(optimized_ver)

        return result


if __name__ == '__main__':  # pragma: no cover
    sel_step = Select_best()
    sel_step.parse_arguments()
    sel_step.setup()
    sel_step.step()
