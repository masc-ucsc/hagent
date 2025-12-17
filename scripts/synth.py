#!/usr/bin/env python3

import argparse
import os
import re
import subprocess
import sys
import tempfile
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
    """Find the best .lib file in tech directory using smart filtering"""
    tech_path = Path(tech_dir)
    if not tech_path.exists():
        return None

    lib_files = list(tech_path.glob('*.lib'))
    if len(lib_files) == 0:
        return None  # No .lib files found
    elif len(lib_files) == 1:
        return str(lib_files[0])

    # Multiple files found - apply smart filtering
    candidates = [str(f) for f in lib_files]

    # Step 1: Filter for typical corner (tt, typ, typical)
    typical_files = [f for f in candidates if any(x in f.lower() for x in ['_tt_', '_typ_', '_typical_'])]
    if typical_files:
        candidates = typical_files

    # Step 2: Filter for 25C temperature
    temp_25_files = [f for f in candidates if '_025c_' in f.lower() or '_25c_' in f.lower()]
    if temp_25_files:
        candidates = temp_25_files

    # Step 3: Filter for medium voltage (1v8, 1.8v, or similar)
    # Look for 1v8, 1.8v patterns
    medium_v_files = [f for f in candidates if any(x in f.lower() for x in ['1v8', '1.8v', '1_8v'])]
    if medium_v_files:
        candidates = medium_v_files

    # If we still have multiple candidates, just pick the first one
    if len(candidates) > 0:
        selected = candidates[0]
        print(f'info: Multiple liberty files found, selected: {Path(selected).name}', file=sys.stderr)
        return selected

    # Fallback: return first from original list
    return str(lib_files[0])


def print_dry_run(args, slang_args, synth_top, elaborate_top):
    """Print command line arguments without executing"""
    print('=== Dry Run Mode ===')

    # Display run modes
    run_modes = []
    if args.run_synth:
        run_modes.append('Synthesis')
    if args.run_elab:
        run_modes.append('Elaboration')
    if args.run_sta:
        run_modes.append('STA')
    print(f'Run modes: {", ".join(run_modes)}')

    if args.run_synth:
        if args.sv2v:
            print('Synthesis flow: sv2v-to-yosys (direct)')
        elif args.no_sv2v:
            print('Synthesis flow: read_slang only (no fallback)')
        else:
            print('Synthesis flow: read_slang with sv2v fallback')
    elif args.run_elab:
        print('Elaboration flow: read_slang with yosys opt only')
    print(f'Liberty file: {args.liberty}')
    print(f'Output netlist: {args.netlist}')
    print(f'Elaboration top: {elaborate_top}')
    print(f'Synthesis top: {synth_top}')
    if args.exclude:
        print(f'Exclude patterns: {args.exclude}')

    # Check for file existence and collect warnings
    warnings = []

    # Check liberty file
    if not Path(args.liberty).exists():
        warnings.append(f'Liberty file not found: {args.liberty}')

    # Check source files from slang_args
    for arg in slang_args:
        # Skip flags and their arguments
        if arg.startswith('-'):
            continue
        # Check if it looks like a file path (has extension or exists)
        if '.' in arg or Path(arg).exists():
            if not Path(arg).exists():
                warnings.append(f'Source file not found: {arg}')

    # Print warnings if any
    if warnings:
        print('\nWarnings:')
        for warning in warnings:
            print(f'  - {warning}', file=sys.stderr)

    # Build slang command arguments
    needs_hierarchy = elaborate_top != synth_top
    keep_hierarchy_flag = '--keep-hierarchy' if needs_hierarchy else ''
    slang_cmd = f'-DSYNTHESIS {keep_hierarchy_flag} {" ".join(slang_args)}'.strip()

    print(f'\nSlang arguments: {slang_cmd}')

    if args.run_synth:
        print(f'\nYosys script would be written to: {synth_top}_yosys.tcl')
        print(f'Command: yosys -m slang -c {synth_top}_yosys.tcl')
        netlist_path = Path(args.netlist)
        stdout_log = netlist_path.parent / f'{netlist_path.stem}_yosys.stdout'
        print(f'Output log would be written to: {stdout_log}')
    elif args.run_elab:
        print(f'\nYosys elaboration script would be written to: {synth_top}_yosys_elab.tcl')
        print(f'Command: yosys -m slang -c {synth_top}_yosys_elab.tcl')
        netlist_path = Path(args.netlist)
        stdout_log = netlist_path.parent / f'{netlist_path.stem}_yosys_elab.stdout'
        print(f'Output log would be written to: {stdout_log}')

    if args.run_sta:
        print(f'\nSTA script would be written to: {synth_top}_opensta.tcl')
        print(f'Command: sta {synth_top}_opensta.tcl')


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
    parser.add_argument('--run-sta', action='store_true', help='Run STA analysis (can be combined with --run-synth)')
    parser.add_argument('--run-synth', action='store_true', help='Run synthesis (always regenerates netlist)')
    parser.add_argument(
        '--run-elab',
        action='store_true',
        help='Run elaboration only (stops after yosys opt, cannot be combined with --run-synth or --run-sta)',
    )
    parser.add_argument('--exclude', action='append', help='Exclude files matching regex pattern (can be used multiple times)')
    parser.add_argument('--top-synthesis', help='Top module for synthesis (when different from elaboration top in --top)')
    parser.add_argument('--dry-run', action='store_true', help='Show command line arguments without executing')
    parser.add_argument('--sv2v', action='store_true', help='Use sv2v-to-yosys flow directly, skipping read_slang')
    parser.add_argument('--no-sv2v', action='store_true', help='Do not fall back to sv2v if read_slang fails')

    # Parse known args to separate our args from slang args
    args, slang_args = parser.parse_known_args()

    # Validate mutually exclusive flags
    if args.sv2v and args.no_sv2v:
        print('error: --sv2v and --no-sv2v cannot be used together', file=sys.stderr)
        sys.exit(1)

    # Validate --run-elab cannot be combined with --run-synth or --run-sta
    if args.run_elab and (args.run_synth or args.run_sta):
        print('error: --run-elab cannot be combined with --run-synth or --run-sta', file=sys.stderr)
        sys.exit(1)

    # If no run mode specified, default to synthesis
    if not (args.run_sta or args.run_synth or args.run_elab):
        args.run_synth = True

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
    elif args.dry_run:
        # In dry-run mode, use placeholder if no liberty file specified
        tech_dir = args.tech_dir or os.environ.get('HAGENT_TECH_DIR')
        if tech_dir:
            liberty_file = f'{tech_dir}/placeholder.lib'
        else:
            liberty_file = '/code/workspace/tech/placeholder.lib'
    else:
        # Try to use tech-dir or HAGENT_TECH_DIR
        tech_dir = args.tech_dir or os.environ.get('HAGENT_TECH_DIR')
        if tech_dir:
            liberty_file = find_liberty_file(tech_dir)
            if liberty_file is None:
                if not Path(tech_dir).exists():
                    print(f'error: tech directory does not exist: {tech_dir}', file=sys.stderr)
                    sys.exit(1)
                else:
                    print(f'error: no .lib files found in {tech_dir}', file=sys.stderr)
                    sys.exit(1)
        else:
            # Try fallback to /code/workspace/tech
            fallback_tech_dir = '/code/workspace/tech'
            if Path(fallback_tech_dir).exists():
                liberty_file = find_liberty_file(fallback_tech_dir)

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

    if args.dry_run:
        print_dry_run(args, slang_args, synth_top, elaborate_top)
    else:
        # Execute requested operations in order: synth/elab first, then STA
        if args.run_synth:
            run_synthesis(args, slang_args, synth_top)
        elif args.run_elab:
            run_elaboration(args, slang_args, synth_top)

        if args.run_sta:
            run_sta(args, slang_args, synth_top)


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


def _generate_yosys_hierarchy_script(slang_cmd, top_name, liberty_path, netlist_path):
    """Generate Yosys TCL script for synthesis with hierarchy handling"""
    # Create unique temp file path for module list
    temp_fd, temp_path = tempfile.mkstemp(suffix='_yosys_modules.txt')
    os.close(temp_fd)  # Close the file descriptor, we'll let yosys write to it

    return f"""yosys read_slang {slang_cmd}
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

# Prioritize: prefer modules matching the pattern exactly up to '$'
# This ensures "ALU" matches "\\ALU$..." but not "\\ALUControl$..."
foreach candidate $candidates {{
    # Remove leading backslash if present
    set clean_name [string trimleft $candidate "\\\\"]
    # Check if it matches: starts with top_name AND followed by '$' (or exact match)
    set matched 0
    if {{$clean_name eq "{top_name}"}} {{
        set matched 1
    }} elseif {{[string first "{top_name}\\$" $clean_name] == 0}} {{
        set matched 1
    }}

    if {{$matched}} {{
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
yosys dfflibmap -liberty {liberty_path}
yosys printattrs
yosys stat
yosys abc -liberty {liberty_path} -dff -keepff -g aig
yosys stat
if {{$top_module ne "{top_name}"}} {{
    puts "Renaming module $top_module to {top_name}"
    yosys rename $top_module {top_name}
}}
yosys write_verilog -simple-lhs {netlist_path}
"""


def _generate_yosys_simple_script(slang_cmd, top_name, liberty_path, netlist_path):
    """Generate simple Yosys TCL script for synthesis without hierarchy"""
    return f"""yosys read_slang {slang_cmd}
yosys hierarchy -top {top_name}
yosys flatten {top_name}
yosys chformal -remove
yosys opt
yosys synth -top {top_name}
yosys dfflibmap -liberty {liberty_path}
yosys printattrs
yosys stat
yosys abc -liberty {liberty_path} -dff -keepff -g aig
yosys stat
yosys write_verilog -simple-lhs {netlist_path}
"""


def _generate_yosys_sv2v_script(tmp_dir, top_name, liberty_path, netlist_path):
    """Generate Yosys TCL script for sv2v fallback synthesis"""
    return f"""yosys read_verilog -sv {tmp_dir}/*.v
yosys hierarchy -top {top_name}
yosys flatten {top_name}
yosys chformal -remove
yosys opt
yosys synth -top {top_name}
yosys dfflibmap -liberty {liberty_path}
yosys printattrs
yosys stat
yosys abc -liberty {liberty_path} -dff -keepff -g aig
yosys stat
yosys write_verilog -simple-lhs {netlist_path}
"""


def _generate_yosys_elaboration_script(slang_cmd, top_name, netlist_path):
    """Generate simple Yosys TCL script for elaboration only (stops after opt)"""
    return f"""yosys read_slang {slang_cmd}
yosys hierarchy -top {top_name}
yosys flatten {top_name}
yosys chformal -remove
yosys opt
yosys write_verilog -simple-lhs {netlist_path}
"""


def _generate_yosys_elaboration_hierarchy_script(slang_cmd, top_name, netlist_path):
    """Generate Yosys TCL script for elaboration with hierarchy handling (stops after opt)"""
    # Create unique temp file path for module list
    temp_fd, temp_path = tempfile.mkstemp(suffix='_yosys_modules.txt')
    os.close(temp_fd)  # Close the file descriptor, we'll let yosys write to it

    return f"""yosys read_slang {slang_cmd}
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

# Prioritize: prefer modules matching the pattern exactly up to '$'
# This ensures "ALU" matches "\\ALU$..." but not "\\ALUControl$..."
foreach candidate $candidates {{
    # Remove leading backslash if present
    set clean_name [string trimleft $candidate "\\\\"]
    # Check if it matches: starts with top_name AND followed by '$' (or exact match)
    set matched 0
    if {{$clean_name eq "{top_name}"}} {{
        set matched 1
    }} elseif {{[string first "{top_name}\\$" $clean_name] == 0}} {{
        set matched 1
    }}

    if {{$matched}} {{
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
if {{$top_module ne "{top_name}"}} {{
    puts "Renaming module $top_module to {top_name}"
    yosys rename $top_module {top_name}
}}
yosys write_verilog -simple-lhs {netlist_path}
"""


def run_elaboration(args, slang_args, top_name):
    """Run elaboration only (stops after yosys opt without synthesis)"""
    # Create parent directories for netlist output if they don't exist
    netlist_path = Path(args.netlist)
    if not netlist_path.parent.exists():
        netlist_path.parent.mkdir(parents=True, exist_ok=True)

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

    # Generate Yosys elaboration script using appropriate template
    if needs_hierarchy:
        yosys_template = _generate_yosys_elaboration_hierarchy_script(slang_cmd, top_name, args.netlist)
    else:
        yosys_template = _generate_yosys_elaboration_script(slang_cmd, top_name, args.netlist)

    # Write the script to {top}_yosys_elab.tcl
    yosys_script_name = f'{top_name}_yosys_elab.tcl'
    with open(yosys_script_name, 'w') as f:
        f.write(yosys_template)

    # Determine stdout log file path based on netlist path
    stdout_log = netlist_path.parent / f'{netlist_path.stem}_yosys_elab.stdout'

    # Run yosys with elaboration script
    try:
        with open(stdout_log, 'w') as log_file:
            subprocess.run(
                ['yosys', '-m', 'slang', '-c', yosys_script_name], stdout=log_file, stderr=subprocess.STDOUT, check=True
            )
        print(f'Elaboration output written to {stdout_log}', file=sys.stderr)
    except subprocess.CalledProcessError as e:
        print(f'error: elaboration failed: {e}', file=sys.stderr)
        sys.exit(1)


def run_sv2v_synthesis(args, slang_args, top_name, stdout_log):
    """Run synthesis using sv2v-to-yosys flow"""
    # Convert SystemVerilog to Verilog and store all converted plain-Verilog files in a temporary directory for Yosys synthesis
    filtered_args = [a for a in slang_args if a.endswith(('.sv', '.v'))]
    tmp_dir = tempfile.mkdtemp(prefix='tmp_', dir=os.getcwd())

    sv2v_cmd = ['sv2v', '-DSYNTHESIS', '-EAlways'] + filtered_args + ['-w' + str(tmp_dir)]
    print('running:', ' '.join(sv2v_cmd))
    subprocess.run(sv2v_cmd, check=True)

    # Generate sv2v fallback Yosys script
    yosys_sv2v_script = _generate_yosys_sv2v_script(tmp_dir, top_name, args.liberty, args.netlist)

    fallback_tcl = f'{top_name}_yosys_sv2v.tcl'
    with open(fallback_tcl, 'w') as f:
        f.write(yosys_sv2v_script)

    with open(stdout_log, 'a') as log_file:
        subprocess.run(['yosys', '-c', fallback_tcl], stdout=log_file, stderr=subprocess.STDOUT, check=True)

    print(f'sv2v-yosys flow completed, output written to {stdout_log}', file=sys.stderr)


def run_synthesis(args, slang_args, top_name):
    # Create parent directories for netlist output if they don't exist
    netlist_path = Path(args.netlist)
    if not netlist_path.parent.exists():
        netlist_path.parent.mkdir(parents=True, exist_ok=True)

    # Check if yosys is available (skip in dry-run mode)
    if not args.dry_run:
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

    # Generate Yosys script using appropriate template
    if needs_hierarchy:
        yosys_template = _generate_yosys_hierarchy_script(slang_cmd, top_name, args.liberty, args.netlist)
    else:
        yosys_template = _generate_yosys_simple_script(slang_cmd, top_name, args.liberty, args.netlist)

    # Write the modified content to {top}_yosys.tcl
    yosys_script_name = f'{top_name}_yosys.tcl'
    with open(yosys_script_name, 'w') as f:
        f.write(yosys_template)

    # Determine stdout log file path based on netlist path
    netlist_path = Path(args.netlist)
    stdout_log = netlist_path.parent / f'{netlist_path.stem}_yosys.stdout'

    # If --sv2v flag is set, skip read_slang and use sv2v directly
    if args.sv2v:
        try:
            run_sv2v_synthesis(args, slang_args, top_name, stdout_log)
        except subprocess.CalledProcessError as e:
            print(f'error: sv2v-yosys flow failed: {e}', file=sys.stderr)
            sys.exit(1)
        return

    # Try read_slang flow first
    slang_success = False
    try:
        with open(stdout_log, 'w') as log_file:
            subprocess.run(
                ['yosys', '-m', 'slang', '-c', yosys_script_name], stdout=log_file, stderr=subprocess.STDOUT, check=True
            )
        print(f'Yosys output written to {stdout_log}', file=sys.stderr)
        slang_success = True
    except subprocess.CalledProcessError as e:
        if args.no_sv2v:
            print(f'error: slang-yosys flow failed: {e}', file=sys.stderr)
            sys.exit(1)
        else:
            print(f'warning: slang-yosys flow failed: {e}, falling back to sv2v', file=sys.stderr)

    # If slang succeeded, we're done
    if slang_success:
        return

    # Fall back to sv2v flow
    try:
        run_sv2v_synthesis(args, slang_args, top_name, stdout_log)
    except subprocess.CalledProcessError as e:
        print(f'error: sv2v-yosys flow also failed: {e}', file=sys.stderr)
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

    # Check if netlist exists
    if not Path(args.netlist).exists():
        print(f'error: netlist not found: {args.netlist}', file=sys.stderr)
        print('hint: run with --run-synth --run-sta to generate netlist and run STA', file=sys.stderr)
        sys.exit(1)

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
