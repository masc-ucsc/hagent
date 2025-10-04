#!/usr/bin/env python3

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path


def find_top_name(slang_args):
    """Extract top module name from slang arguments"""
    for i, arg in enumerate(slang_args):
        if arg == '--top' and i + 1 < len(slang_args):
            return slang_args[i + 1]
    return None


def filter_args_and_patch_filelists(slang_args, exclude_patterns):
    """Filter slang_args and patch any filelist files to exclude matching patterns"""
    if not exclude_patterns:
        return slang_args

    filtered_args = []
    i = 0

    while i < len(slang_args):
        arg = slang_args[i]

        # Check if this argument should be excluded
        excluded = False
        for pattern in exclude_patterns:
            if re.search(pattern, arg):
                excluded = True
                break

        if excluded:
            i += 1
            continue

        # Check if this is a filelist argument (-f or -F)
        if arg in ['-f', '-F'] and i + 1 < len(slang_args):
            # Next argument should be the filelist path
            filelist_path = slang_args[i + 1]
            patched_path = patch_filelist(filelist_path, exclude_patterns)

            filtered_args.append(arg)
            filtered_args.append(patched_path)
            i += 2  # Skip both the flag and the path
        else:
            filtered_args.append(arg)
            i += 1

    return filtered_args


def patch_filelist(filelist_path, exclude_patterns):
    """Create a patched filelist with excluded patterns removed"""
    filelist_file = Path(filelist_path)
    if not filelist_file.exists():
        return filelist_path

    # Read the original filelist
    with open(filelist_file, 'r') as f:
        lines = f.readlines()

    # Filter out lines matching exclude patterns
    filtered_lines = []
    excluded_any = False

    for line in lines:
        line_stripped = line.strip()
        excluded = False

        for pattern in exclude_patterns:
            if re.search(pattern, line_stripped):
                excluded = True
                excluded_any = True
                break

        if not excluded:
            filtered_lines.append(line)

    # If no lines were excluded, return original path
    if not excluded_any:
        return filelist_path

    # Create patched filelist path
    patched_path = filelist_file.parent / f'patched_{filelist_file.name}'

    # Write the filtered content
    with open(patched_path, 'w') as f:
        f.writelines(filtered_lines)

    return str(patched_path)


def find_liberty_file(tech_dir):
    """Find the single .lib file in tech directory"""
    tech_path = Path(tech_dir)
    if not tech_path.exists():
        return None

    lib_files = list(tech_path.glob('*.lib'))
    if len(lib_files) == 1:
        return str(lib_files[0])
    elif len(lib_files) > 1:
        return None  # Multiple files found, require explicit --liberty
    else:
        return None  # No .lib files found


def main():
    # Show help if no arguments provided
    if len(sys.argv) == 1:
        sys.argv.append('-h')

    parser = argparse.ArgumentParser(
        description='Run yosys synthesis with slang frontend',
        epilog='All other arguments are passed to read_slang command. Example: synth.py --netlist out.v --top cpu input.sv',
    )
    parser.add_argument('--liberty', help='Liberty file path')
    parser.add_argument('--tech-dir', help='Technology directory path (defaults to HAGENT_TECH_DIR env var)')
    parser.add_argument('--netlist', default='netlist.v', help='Output netlist file path (default: netlist.v)')
    parser.add_argument('--sta', action='store_true', help='Run STA analysis instead of synthesis')
    parser.add_argument('--exclude', action='append', help='Exclude files matching regex pattern (can be used multiple times)')

    # Parse known args to separate our args from slang args
    args, slang_args = parser.parse_known_args()

    # Handle liberty file logic
    liberty_file = None
    if args.liberty:
        liberty_file = args.liberty
    else:
        # Try to use tech-dir or HAGENT_TECH_DIR
        tech_dir = args.tech_dir or os.environ.get('HAGENT_TECH_DIR')
        if tech_dir:
            liberty_file = find_liberty_file(tech_dir)
            if liberty_file is None:
                if not Path(tech_dir).exists():
                    print(f'error: tech directory does not exist: {tech_dir}', file=sys.stderr)
                    sys.exit(1)
                lib_files = list(Path(tech_dir).glob('*.lib'))
                if len(lib_files) > 1:
                    print(f'error: multiple .lib files found in {tech_dir}, use --liberty to specify which one', file=sys.stderr)
                    sys.exit(1)
                elif len(lib_files) == 0:
                    print(f'error: no .lib files found in {tech_dir}', file=sys.stderr)
                    sys.exit(1)
        else:
            print('error: either --liberty or --tech-dir (or HAGENT_TECH_DIR env var) must be specified', file=sys.stderr)
            sys.exit(1)

    # Store the liberty file in args for later use
    args.liberty = liberty_file

    # Apply exclude patterns to filter arguments and patch filelists
    if args.exclude:
        slang_args = filter_args_and_patch_filelists(slang_args, args.exclude)

    # Extract top module name
    top_name = find_top_name(slang_args)
    if not top_name:
        print('error: --top <module_name> is required', file=sys.stderr)
        parser.print_help()
        sys.exit(1)

    if args.sta:
        run_sta(args, slang_args, top_name)
    else:
        run_synthesis(args, slang_args, top_name)


def needs_recompilation(slang_args, netlist_path):
    """Check if netlist is older than any source file"""
    if not Path(netlist_path).exists():
        return True

    netlist_mtime = Path(netlist_path).stat().st_mtime

    # Extract source files from slang args (files without -- prefix)
    for arg in slang_args:
        if not arg.startswith('-') and Path(arg).exists():
            if Path(arg).stat().st_mtime > netlist_mtime:
                return True

    return False


def run_synthesis(args, slang_args, top_name):
    # Check if yosys is available
    if subprocess.run(['which', 'yosys'], capture_output=True).returncode != 0:
        print('error: synth.py yosys tool is not in the path', file=sys.stderr)
        sys.exit(1)

    # Check if yosys-slang module is available
    result = subprocess.run(['yosys', '-m', 'slang', '-p', 'help read_slang'], capture_output=True, text=True)
    if result.returncode != 0:
        print('error: synth.py yosys-slang module is not installed', file=sys.stderr)
        sys.exit(1)

    # Build slang command arguments with synthesis define
    slang_cmd = f'-DSYNTHESIS {" ".join(slang_args)}'

    # Yosys script template using read_slang
    yosys_template = f"""read_slang {slang_cmd}
hierarchy -top {top_name}
flatten {top_name}
opt
synth -top {top_name}
dfflibmap -liberty {args.liberty}
printattrs
stat
abc -liberty {args.liberty} -dff -keepff -g aig
stat
write_verilog {args.netlist}
"""

    # Write the modified content to {top}_yosys.s
    yosys_script_name = f'{top_name}_yosys.s'
    with open(yosys_script_name, 'w') as f:
        f.write(yosys_template)

    # Run yosys with slang module and the script
    try:
        subprocess.run(['yosys', '-m', 'slang', '-s', yosys_script_name], check=True)
    except subprocess.CalledProcessError as e:
        print(f'Error running yosys: {e}', file=sys.stderr)
        sys.exit(1)


def find_clock_signal(netlist_path):
    """Find clock signal in netlist module ports (clk or clock)"""
    if not Path(netlist_path).exists():
        return None

    with open(netlist_path, 'r') as f:
        content = f.read()

    # Look for module declaration and extract ports
    import re

    module_match = re.search(r'module\s+\w+\s*\((.*?)\);', content, re.DOTALL)
    if not module_match:
        return None

    ports_section = module_match.group(1)

    # Look for clock signals in the ports
    if re.search(r'\bclk\b', ports_section):
        return 'clk'
    elif re.search(r'\bclock\b', ports_section):
        return 'clock'

    return None


def run_sta(args, slang_args, top_name):
    # Check if sta is available
    if subprocess.run(['which', 'sta'], capture_output=True).returncode != 0:
        print('error: synth.py sta tool is not in the path', file=sys.stderr)
        sys.exit(1)

    # Check if we need to recompile
    if needs_recompilation(slang_args, args.netlist):
        print('Netlist is outdated, running synthesis first...')
        run_synthesis(args, slang_args, top_name)

    # Find clock signal
    clock_signal = find_clock_signal(args.netlist)

    # Check if VCD file exists (assume same directory as netlist)
    netlist_path = Path(args.netlist)
    vcd_path = netlist_path.parent / f'{netlist_path.stem}.vcd'
    vcd_exists = vcd_path.exists()

    # Build STA script dynamically
    sta_script = f"""read_liberty {args.liberty}
read_verilog {args.netlist}
link_design {top_name}
"""

    # Add clock creation if clock signal exists
    if clock_signal:
        sta_script += f'create_clock -name {clock_signal} -period 1 {{{clock_signal}}}\n'
        # Add input/output delays for meaningful timing analysis
        sta_script += f'set_input_delay -clock {clock_signal} 0.1 [all_inputs]\n'
        sta_script += f'set_output_delay -clock {clock_signal} 0.1 [all_outputs]\n'

    # Add power analysis if VCD exists
    if vcd_exists:
        sta_script += f"""read_power_activities -vcd {vcd_path}
report_power
"""

    # Add timing analysis
    sta_script += """report_checks
exit
"""

    # Write the modified content to {top}_opensta.tcl
    sta_script_name = f'{top_name}_opensta.tcl'
    with open(sta_script_name, 'w') as f:
        f.write(sta_script)

    # Run sta with the modified script
    try:
        subprocess.run(['sta', sta_script_name], check=True)
    except subprocess.CalledProcessError as e:
        print(f'Error running sta: {e}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
