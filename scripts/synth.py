#!/usr/bin/env python3
# See LICENSE for details

import argparse
import datetime
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


def _check_tool_available(tool_name):
    """Check if a tool is available in PATH"""
    if subprocess.run(['which', tool_name], capture_output=True).returncode != 0:
        print(f'error: {tool_name} tool is not in the path', file=sys.stderr)
        sys.exit(1)


def _run_tool_with_script(tool_cmd, script_content, script_path, log_path, phase_name):
    """Execute a tool with a script and capture output to log"""
    # Write script
    with open(script_path, 'w') as f:
        f.write(script_content)

    # Execute with logging
    with open(log_path, 'w') as log:
        subprocess.run(tool_cmd, stdout=log, stderr=subprocess.STDOUT, check=True)

    # Report completion
    print(f'{phase_name} complete', file=sys.stderr)
    print(f'Log: {log_path}', file=sys.stderr)


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
    print(f'Output directory: {args.output_dir}')
    print(f'Elaboration method: {args.elab_method}')

    # Determine which phases will run
    no_run_flags = not (args.run_elab or args.run_synth or args.run_sta)
    run_elab = no_run_flags or args.run_elab or args.run_synth
    run_synth = no_run_flags or args.run_synth
    run_sta = no_run_flags or args.run_sta

    # Display phases
    phases = []
    if not args.skip_elab and run_elab:
        phases.append('Elaboration → elab.v')
    elif args.skip_elab:
        phases.append('(Skip elaboration, reuse elab.v)')
    if run_synth:
        phases.append('Synthesis → synth.v')
    if run_sta:
        phases.append('STA')
    print(f'Phases: {" → ".join(phases)}')

    print(f'Liberty file: {args.liberty}')
    print(f'Elaboration top: {elaborate_top}')
    print(f'Synthesis top: {synth_top}')
    if args.exclude:
        print(f'Exclude patterns: {args.exclude}')

    # Check for file existence and collect warnings
    warnings = []

    # Check liberty file
    if args.liberty and not Path(args.liberty).exists():
        warnings.append(f'Liberty file not found: {args.liberty}')

    # Check source files from slang_args
    for arg in slang_args:
        if arg.startswith('-'):
            continue
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

    output_dir = Path(args.output_dir)
    if run_elab:
        print(f'\nElaboration script: {output_dir / "elab.tcl"}')
        print(f'Elaboration output: {output_dir / "elab.v"}')
        print(f'Elaboration log: {output_dir / "elab.log"}')

    if run_synth:
        print(f'\nSynthesis script: {output_dir / "synth.tcl"}')
        print(f'Synthesis output: {output_dir / "synth.v"}')
        print(f'Synthesis log: {output_dir / "synth.log"}')

    if run_sta:
        print(f'\nSTA script: {output_dir / "sta.tcl"}')
        print(f'STA log: {output_dir / "sta.log"}')
        print(f'STA command: sta {output_dir / "sta.tcl"}')


def _ensure_output_dir(path):
    output_dir = Path(path)
    if output_dir.exists():
        if not output_dir.is_dir():
            print(f'error: output path exists but is not a directory: {output_dir}', file=sys.stderr)
            sys.exit(1)
        return output_dir
    try:
        output_dir.mkdir(parents=True, exist_ok=False)
    except OSError as exc:
        print(f'error: unable to create output directory {output_dir}: {exc}', file=sys.stderr)
        sys.exit(1)
    return output_dir


def _write_manifest(output_dir, args, slang_args, top_module):
    """Write manifest.yaml with synthesis metadata"""
    # Extract input files from slang_args (files that exist and aren't flags)
    input_files = []
    for arg in slang_args:
        if not arg.startswith('-') and Path(arg).exists():
            input_files.append(arg)

    # Build YAML content manually (simple key-value pairs and lists)
    manifest_path = output_dir / 'manifest.yaml'
    with open(manifest_path, 'w') as f:
        # Top-level fields
        f.write(f'tag: {args.tag}\n')
        f.write(f'timestamp: {datetime.datetime.now(datetime.timezone.utc).isoformat()}\n')
        f.write(f'top_module: {top_module}\n')

        # Input files list
        f.write('input_files:\n')
        if input_files:
            for file in input_files:
                f.write(f'  - {file}\n')
        else:
            f.write('  []\n')

        # Environment info
        f.write(f'docker_image: {os.environ.get("HAGENT_DOCKER", "none")}\n')
        f.write(f'liberty_file: {args.liberty or "none"}\n')

        # Synthesis args (nested)
        f.write('synthesis_args:\n')
        f.write(f'  elab_method: {args.elab_method}\n')
        f.write('  exclude_patterns:\n')
        if args.exclude:
            for pattern in args.exclude:
                f.write(f'    - {pattern}\n')
        else:
            f.write('    []\n')
        f.write(f'  skip_elab: {args.skip_elab}\n')

        # Slang args list
        f.write('slang_args:\n')
        if slang_args:
            for arg in slang_args:
                f.write(f'  - {arg}\n')
        else:
            f.write('  []\n')

    print(f'Manifest: {manifest_path}', file=sys.stderr)


def main():
    # Show help if no arguments provided
    if len(sys.argv) == 1:
        sys.argv.append('-h')

    # Handle -- separator for slang arguments (GNU standard)
    # Preferred: synth.py --tag baseline --dir build/ -- --top ALU alu.sv
    # Fallback: synth.py --tag baseline --dir build/ --top ALU alu.sv (parse_known_args)
    if '--' in sys.argv:
        sep_idx = sys.argv.index('--')
        synth_argv = sys.argv[1:sep_idx]
        slang_args = sys.argv[sep_idx + 1 :]
        use_separator = True
    else:
        synth_argv = None  # Will use parse_known_args() fallback
        slang_args = None
        use_separator = False

    parser = argparse.ArgumentParser(
        description='Run yosys synthesis with slang frontend',
        epilog='Use -- to separate synth.py args from slang args. Example: synth.py --tag baseline --dir build/ -- --top ALU input.sv',
    )
    parser.add_argument('--liberty', help='Liberty file path')
    parser.add_argument('--tech-dir', help='Technology directory path (defaults to HAGENT_TECH_DIR env var)')
    parser.add_argument(
        '--dir',
        help='Base directory for outputs (default: HAGENT_CACHE_DIR when --tag used)',
    )
    # Backward compatibility - hidden deprecated argument
    parser.add_argument(
        '--output-dir',
        '-o',
        dest='dir',
        help=argparse.SUPPRESS,
    )
    parser.add_argument(
        '--tag',
        help='Tag name for this synthesis run (creates <dir>/<tag>/ subdirectory with manifest)',
    )
    parser.add_argument(
        '--run-elab',
        action='store_true',
        help='Only run elaboration (create elab.v only, disables default synth+STA)',
    )
    parser.add_argument(
        '--run-synth',
        action='store_true',
        help='Run elaboration + synthesis (create elab.v + synth.v, disables default STA)',
    )
    parser.add_argument(
        '--run-sta',
        action='store_true',
        help='Run STA on synth.v (use alone to run only STA without elab/synth)',
    )
    parser.add_argument(
        '--skip-elab',
        action='store_true',
        help='Skip elaboration if elab.v exists and is up-to-date (useful for fast iteration)',
    )
    parser.add_argument(
        '--elab-method',
        choices=['auto', 'slang', 'sv2v'],
        default='auto',
        help='Elaboration method: auto (try slang, fallback to sv2v), slang (read_slang only), sv2v (sv2v only)',
    )
    parser.add_argument('--exclude', action='append', help='Exclude files matching regex pattern (can be used multiple times)')
    parser.add_argument('--top-synthesis', help='Top module for synthesis (when different from elaboration top in --top)')
    parser.add_argument('--dry-run', action='store_true', help='Show command line arguments without executing')

    # Parse args using -- separator or fallback to parse_known_args
    if use_separator:
        args = parser.parse_args(synth_argv)
    else:
        args, slang_args = parser.parse_known_args()

    # Validate --tag (no slashes, no special chars except dash/underscore)
    if args.tag:
        import re

        if not re.match(r'^[a-zA-Z0-9_-]+$', args.tag):
            print('error: --tag must contain only alphanumeric characters, dash, or underscore', file=sys.stderr)
            sys.exit(1)

    # Directory resolution logic
    # 1. If --tag + --dir: use <dir>/<tag>/
    # 2. If --tag only: use HAGENT_CACHE_DIR/<tag>/
    # 3. If --dir only (no tag): use <dir>/ directly (legacy mode)
    if args.tag and args.dir:
        output_dir_path = Path(args.dir) / args.tag
    elif args.tag:
        # Use HAGENT_CACHE_DIR for tagged builds without explicit --dir
        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if not cache_dir:
            print('error: --tag requires either --dir or HAGENT_CACHE_DIR environment variable', file=sys.stderr)
            sys.exit(1)
        output_dir_path = Path(cache_dir) / args.tag
    elif args.dir:
        # Legacy mode: --dir without --tag
        output_dir_path = Path(args.dir)
    else:
        print('error: either --dir or --tag (with HAGENT_CACHE_DIR) is required', file=sys.stderr)
        sys.exit(1)

    # Create output directory and store standard paths
    output_dir = _ensure_output_dir(output_dir_path)
    args.elab_path = output_dir / 'elab.v'
    args.netlist_path = output_dir / 'synth.v'
    args.output_dir = str(output_dir)  # For compatibility with rest of code

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
        # Determine which phases to run
        # Default: all phases (elab + synth + STA) if no --run-* flags specified
        no_run_flags = not (args.run_elab or args.run_synth or args.run_sta)

        should_run_elab = no_run_flags or args.run_elab or args.run_synth
        should_run_synth = no_run_flags or args.run_synth
        should_run_sta = no_run_flags or args.run_sta

        # Phase 1: Elaborate (unless --skip-elab and elab.v exists)
        if should_run_elab and not (args.skip_elab and args.elab_path.exists()):
            run_elaboration(args, slang_args, synth_top)

        # Phase 2: Synthesize if requested
        if should_run_synth:
            run_synthesis(args, synth_top)

        # Phase 3: STA if requested
        if should_run_sta:
            run_sta(args, synth_top)

        # Generate manifest.yaml when --tag is used
        if args.tag:
            _write_manifest(output_dir, args, slang_args, synth_top)


def _generate_yosys_elaboration_script(slang_cmd, top_name, netlist_path):
    """Generate simple Yosys TCL script for elaboration only (stops after opt)"""
    return f"""yosys read_slang {slang_cmd}
yosys hierarchy -top {top_name}
yosys flatten {top_name}
yosys chformal -remove
yosys opt
yosys write_verilog -simple-lhs {netlist_path}
"""


def _generate_yosys_elaboration_hierarchy_script(slang_cmd, top_name, netlist_path, output_dir):
    """Generate Yosys TCL script for elaboration with hierarchy handling (stops after opt)"""
    # Use output directory for hierarchy file
    hierarchy_file = output_dir / 'hierarchy.txt'

    return f"""yosys read_slang {slang_cmd}
yosys tee -q -o {hierarchy_file} ls
set fp [open "{hierarchy_file}" r]
set mods [read $fp]
close $fp
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
    """Run elaboration phase (produces elab.v)"""
    _check_tool_available('yosys')

    # Determine elaboration method
    if args.elab_method == 'sv2v':
        _elaborate_with_sv2v(args, slang_args, top_name)
    elif args.elab_method == 'slang':
        _elaborate_with_readslang(args, slang_args, top_name)
    else:  # auto
        try:
            _elaborate_with_readslang(args, slang_args, top_name)
        except subprocess.CalledProcessError as e:
            print(f'read_slang failed: {e}, falling back to sv2v', file=sys.stderr)
            _elaborate_with_sv2v(args, slang_args, top_name)


def _elaborate_with_readslang(args, slang_args, top_name):
    """Elaborate using read_slang"""
    output_dir = Path(args.output_dir)
    elab_path = args.elab_path

    # Check yosys-slang module
    result = subprocess.run(['yosys', '-m', 'slang', '-p', 'help read_slang'], capture_output=True, text=True)
    if result.returncode != 0:
        print('error: yosys-slang module is not installed', file=sys.stderr)
        sys.exit(1)

    # Determine if we need hierarchy handling
    elaborate_top = find_top_name(slang_args)
    needs_hierarchy = elaborate_top != top_name

    # Build slang command
    keep_hierarchy_flag = '--keep-hierarchy' if needs_hierarchy else ''
    slang_cmd = f'-DSYNTHESIS {keep_hierarchy_flag} {" ".join(slang_args)}'.strip()

    # Generate script
    if needs_hierarchy:
        script = _generate_yosys_elaboration_hierarchy_script(slang_cmd, top_name, elab_path, output_dir)
    else:
        script = _generate_yosys_elaboration_script(slang_cmd, top_name, elab_path)

    # Execute
    _run_tool_with_script(
        ['yosys', '-m', 'slang', '-c', str(output_dir / 'elab.tcl')],
        script,
        output_dir / 'elab.tcl',
        output_dir / 'elab.log',
        f'Elaboration: {elab_path}',
    )


def _elaborate_with_sv2v(args, slang_args, top_name):
    """Elaborate using sv2v"""
    output_dir = Path(args.output_dir)
    elab_path = args.elab_path

    # Run sv2v
    sv_files = [a for a in slang_args if a.endswith(('.sv', '.v'))]
    tmp_dir = output_dir / 'sv2v_tmp'
    tmp_dir.mkdir(exist_ok=True)

    sv2v_cmd = ['sv2v', '-DSYNTHESIS', '-EAlways'] + sv_files + ['-w', str(tmp_dir)]
    print(f'Running sv2v: {" ".join(sv2v_cmd)}', file=sys.stderr)
    subprocess.run(sv2v_cmd, check=True)

    # Elaborate with read_verilog
    script = f"""yosys read_verilog -sv {tmp_dir}/*.v
yosys hierarchy -top {top_name}
yosys flatten {top_name}
yosys chformal -remove
yosys opt
yosys write_verilog -simple-lhs {elab_path}
"""

    # Execute
    _run_tool_with_script(
        ['yosys', '-c', str(output_dir / 'elab.tcl')],
        script,
        output_dir / 'elab.tcl',
        output_dir / 'elab.log',
        f'Elaboration (sv2v): {elab_path}',
    )


def run_synthesis(args, top_name):
    """Run synthesis phase (reads elab.v, produces synth.v)"""
    output_dir = Path(args.output_dir)
    elab_path = args.elab_path
    netlist_path = args.netlist_path

    # Verify elab.v exists
    if not elab_path.exists():
        print(f'error: Elaboration file not found: {elab_path}', file=sys.stderr)
        print('hint: Run elaboration first (without --skip-elab)', file=sys.stderr)
        sys.exit(1)

    # Generate synthesis script
    script = f"""yosys read_verilog -sv {elab_path}
yosys hierarchy -top {top_name}
yosys synth -top {top_name}
yosys dfflibmap -liberty {args.liberty}
yosys printattrs
yosys stat
yosys abc -liberty {args.liberty} -dff -keepff -g aig
yosys stat
yosys write_verilog -simple-lhs {netlist_path}
"""

    # Execute
    _run_tool_with_script(
        ['yosys', '-c', str(output_dir / 'synth.tcl')],
        script,
        output_dir / 'synth.tcl',
        output_dir / 'synth.log',
        f'Synthesis: {netlist_path}',
    )


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


def run_sta(args, top_name):
    """Run STA on synthesized design"""
    output_dir = Path(args.output_dir)
    netlist_path = args.netlist_path

    _check_tool_available('sta')

    # Check if synth.v exists
    if not netlist_path.exists():
        print(f'error: Synthesized design not found: {netlist_path}', file=sys.stderr)
        print('hint: Run synthesis first with --run-synth or default mode', file=sys.stderr)
        sys.exit(1)

    # Find clock signal
    clock_signal = find_clock_signal(str(netlist_path))

    # Check if VCD file exists (assume same directory as netlist)
    vcd_path = netlist_path.parent / f'{netlist_path.stem}.vcd'
    vcd_exists = vcd_path.exists()

    # Build STA script dynamically
    sta_script = f"""read_liberty {args.liberty}
read_verilog {netlist_path}
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

    # Execute
    try:
        _run_tool_with_script(
            ['sta', str(output_dir / 'sta.tcl')],
            sta_script,
            output_dir / 'sta.tcl',
            output_dir / 'sta.log',
            'STA',
        )
    except subprocess.CalledProcessError as e:
        print(f'Error running STA: {e}', file=sys.stderr)
        print(f'See log: {output_dir / "sta.log"}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
