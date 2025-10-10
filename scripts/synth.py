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
    parser.add_argument('--top-synthesis', help='Top module for synthesis (when different from elaboration top in --top)')

    # Parse known args to separate our args from slang args
    args, slang_args = parser.parse_known_args()

    # Check if --top was in the original arguments but not in slang_args
    # This happens when --top appears before other arguments
    top_from_argv = None
    for i, arg in enumerate(sys.argv):
        if arg == '--top' and i + 1 < len(sys.argv):
            top_from_argv = sys.argv[i + 1]
            # Add it back to slang_args if not already there
            if '--top' not in slang_args:
                slang_args = ['--top', top_from_argv] + slang_args
            break

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
            # Try fallback to /code/workspace/tech
            fallback_tech_dir = '/code/workspace/tech'
            if Path(fallback_tech_dir).exists():
                liberty_file = find_liberty_file(fallback_tech_dir)
                if liberty_file is None:
                    lib_files = list(Path(fallback_tech_dir).glob('*.lib'))
                    if len(lib_files) > 1:
                        print(
                            f'error: multiple .lib files found in {fallback_tech_dir}, use --liberty to specify which one',
                            file=sys.stderr,
                        )
                        sys.exit(1)

            if liberty_file is None:
                print('error: either --liberty or --tech-dir (or HAGENT_TECH_DIR env var) must be specified', file=sys.stderr)
                sys.exit(1)

    # Store the liberty file in args for later use
    args.liberty = liberty_file

    # Apply exclude patterns to filter arguments and patch filelists
    if args.exclude:
        slang_args = filter_args_and_patch_filelists(slang_args, args.exclude)

    # Extract top module name from slang args
    elaborate_top = find_top_name(slang_args)
    if not elaborate_top:
        print('error: --top <module_name> is required', file=sys.stderr)
        parser.print_help()
        sys.exit(1)

    # Determine synthesis top (may differ from elaborate top)
    synth_top = args.top_synthesis if args.top_synthesis else elaborate_top

    if args.sta:
        run_sta(args, slang_args, synth_top)
    else:
        run_synthesis(args, slang_args, synth_top)


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

    # Determine if we need --keep-hierarchy
    elaborate_top = find_top_name(slang_args)
    needs_hierarchy = elaborate_top != top_name

    # Build slang command arguments with synthesis define
    # Note: slang_args already contains --top for elaboration
    keep_hierarchy_flag = '--keep-hierarchy' if needs_hierarchy else ''
    slang_cmd = f'-DSYNTHESIS {keep_hierarchy_flag} {" ".join(slang_args)}'.strip()

    # Yosys script template using read_slang with TCL
    # If we need hierarchy, use TCL to find the matching module
    if needs_hierarchy:
        import tempfile
        import os

        # Create unique temp file path
        temp_fd, temp_path = tempfile.mkstemp(suffix='_yosys_modules.txt')
        os.close(temp_fd)  # Close the file descriptor, we'll let yosys write to it

        yosys_template = f"""yosys read_slang {slang_cmd}
yosys tee -q -o {temp_path} ls
set fp [open "{temp_path}" r]
set mods [read $fp]
close $fp
file delete {temp_path}
set lines [split $mods "\\n"]
set top_module ""
set candidates [list]
set rejected [list]

# Collect all matching candidates
foreach line $lines {{
    set trimmed [string trim $line]
    if {{$trimmed ne "" && [string first "{top_name}" $trimmed] >= 0 && [string first "modules:" $trimmed] < 0 && [string first "memories:" $trimmed] < 0 && [string first "processes:" $trimmed] < 0}} {{
        lappend candidates $trimmed
    }}
}}

# Prioritize: prefer modules starting with the target name (possibly with backslash)
foreach candidate $candidates {{
    # Remove leading backslash if present
    set clean_name [string trimleft $candidate "\\\\"]
    # Check if it starts with the top_name
    if {{[string first "{top_name}" $clean_name] == 0}} {{
        if {{$top_module eq ""}} {{
            set top_module $candidate
        }} else {{
            lappend rejected $candidate
        }}
    }} else {{
        lappend rejected $candidate
    }}
}}

# If no prioritized match, take the first candidate
if {{$top_module eq "" && [llength $candidates] > 0}} {{
    set top_module [lindex $candidates 0]
    set rejected [lrange $candidates 1 end]
}}

if {{$top_module eq ""}} {{
    error "Could not find module matching '{top_name}'"
}}

puts "Selected module: $top_module"
puts stderr "info: Selected module: $top_module"
if {{[llength $rejected] > 0}} {{
    puts "Rejected candidates:"
    puts stderr "info: Rejected [llength $rejected] candidate(s)"
    foreach rej $rejected {{
        puts "  - $rej"
    }}
}}
yosys hierarchy -top $top_module
yosys flatten
yosys chformal -remove
yosys opt
yosys synth
yosys dfflibmap -liberty {args.liberty}
yosys printattrs
yosys stat
yosys abc -liberty {args.liberty} -dff -keepff -g aig
yosys stat
if {{$top_module ne "{top_name}"}} {{
    puts "Renaming module $top_module to {top_name}"
    yosys rename $top_module {top_name}
}}
yosys write_verilog {args.netlist}
"""
    else:
        yosys_template = f"""yosys read_slang {slang_cmd}
yosys hierarchy -top {top_name}
yosys flatten {top_name}
yosys chformal -remove
yosys opt
yosys synth -top {top_name}
yosys dfflibmap -liberty {args.liberty}
yosys printattrs
yosys stat
yosys abc -liberty {args.liberty} -dff -keepff -g aig
yosys stat
yosys write_verilog {args.netlist}
"""

    # Write the modified content to {top}_yosys.tcl
    yosys_script_name = f'{top_name}_yosys.tcl'
    with open(yosys_script_name, 'w') as f:
        f.write(yosys_template)

    # Determine stdout log file path based on netlist path
    netlist_path = Path(args.netlist)
    stdout_log = netlist_path.parent / f'{netlist_path.stem}_yosys.stdout'

    # Run yosys with slang module and TCL mode, redirect output
    try:
        with open(stdout_log, 'w') as log_file:
            subprocess.run(
                ['yosys', '-m', 'slang', '-c', yosys_script_name], stdout=log_file, stderr=subprocess.STDOUT, check=True
            )
        print(f'Yosys output written to {stdout_log}', file=sys.stderr)
    except subprocess.CalledProcessError as e:
        print(f'Error running yosys: {e}', file=sys.stderr)
        print(f'Check {stdout_log} for details', file=sys.stderr)
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

    # Extract all port names
    port_matches = re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', ports_section)

    # Look for exact clock signals first
    if 'clk' in port_matches:
        return 'clk'
    elif 'clock' in port_matches:
        return 'clock'

    # Fall back to finding any signal with "clk" or "clock" substring
    for port in port_matches:
        if 'clk' in port.lower() or 'clock' in port.lower():
            return port

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
