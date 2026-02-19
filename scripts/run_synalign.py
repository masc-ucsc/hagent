#!/usr/bin/env python3
# See LICENSE for details
"""
Script to run SynAlign via LiveHD's lgshell.

Creates color.json from the timing report, invokes lgshell with inou.traverse_lg,
and prints the structured net-to-RTL mapping output.

Usage:
    python scripts/run_synalign.py \
        --timing-report <path> --netlist <path> --liberty <path> \
        --lgshell <path> --synth-top <name> --orig-top <name> --elab-top <name> \
        [--standalone-files f1 f2 ...] [--manifest-file <path>] \
        [--output-dir <path>]
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path


def extract_nodes(timing_report_file: str) -> list[str]:
    """Extract critcal path node names from timing report sections where Path Group is clock or similar."""
    nodes: list[str] = []
    node_pattern = re.compile(r'[\^v]\s+(\w+)/')
    in_clock_path = False

    with open(timing_report_file) as f:
        for line in f:
            if 'Path Group:' in line:
                group_name = line.split(':', 1)[1].strip()
                in_clock_path = group_name == 'clock' or group_name == 'clk' or group_name == 'clk_i'
                continue

            if in_clock_path:
                matches = node_pattern.findall(line)
                for match in matches:
                    if match not in nodes:
                        nodes.append(match)

    return nodes


def create_color_json(module_name: str, nodes: list[str], output_file: str = 'color.json') -> str:
    """Create color.json with node-to-color mapping for lgshell inou.attr.load."""
    node_colors = {node: i + 1 for i, node in enumerate(nodes)}

    data = [
        {
            'class': 'livehd.lgraph.color',
            'modules': [
                {
                    'name': module_name,
                    'node_colors': node_colors,
                }
            ],
        }
    ]

    with open(output_file, 'w') as f:
        json.dump(data, f, indent=4)

    return output_file


def build_lgshell_command(
    liberty_file: str,
    synth_top: str,
    netlist_path: str,
    orig_top: str,
    elab_top: str,
    standalone_files: list[str] | None = None,
    manifest_file: str | None = None,
    color_json: str = 'color.json',
) -> str:
    """Build the lgshell pipeline command string for synalign."""
    # Note that we always add double quotes around the top name to allow lgshell
    # to read names with special characters inserte by yosys like '$'
    parts = [
        f'inou.liberty files:{liberty_file}',
        f'inou.yosys.tolg top:"{synth_top}" files:{netlist_path}',
        f'inou.attr.load files:{color_json}',
    ]

    # Build the original RTL load command
    orig_cmd = f'inou.yosys.tolg top:"{orig_top}" elab_top:"{elab_top}" frontend:slang slang_flags:--keep-hierarchy'

    if standalone_files:
        orig_cmd += f' files:{",".join(standalone_files)}'
    if manifest_file:
        orig_cmd += f' filelist_file:{manifest_file}'

    parts.append(orig_cmd)
    parts.append(f'lgraph.open name:"{orig_top}"')
    parts.append(f'lgraph.open name:"{synth_top}"')
    parts.append(f'inou.traverse_lg LGorig:"{orig_top}" LGsynth:"{synth_top}"')

    return ' |> '.join(parts)


def parse_synalign_output(stdout: str) -> dict:
    """
    Parse LiveHD inou.traverse_lg stdout into a structured mapping.

    Looks for the "Reporting final critical resolved matches:" marker, then parses
    lines in the actual output format:
        <synth_node>,<synth_inst>  :-  <orig_info>  --  <color>  --  [<line>,<col>]<path>

    Returns:
        Dictionary with 'mappings' list and 'raw_output' string.
    """
    mappings = []
    found_marker = False

    # Regex for [line,col]path (same approach as comment_rtl.py)
    loc_pattern = re.compile(r'\[\s*(\d+)\s*,\s*\d+\s*\]((\.\./)*[^ \t\r\n]+)')

    for line in stdout.splitlines():
        if 'Reporting final critical resolved matches:' in line:
            found_marker = True
            continue

        if not found_marker:
            continue

        # Skip blank lines or lines that don't look like mapping output
        stripped = line.strip()
        if not stripped or ':-' not in stripped:
            continue

        # Split on ':-' to get synth side and orig side
        parts = stripped.split(':-', 1)
        if len(parts) != 2:
            continue

        synth_part = parts[0].strip()
        orig_part = parts[1].strip()

        # Parse synth_node,synth_instance from left side
        synth_fields = synth_part.split(',', 1)
        synth_node = synth_fields[0].strip()
        synth_instance = synth_fields[1].strip() if len(synth_fields) > 1 else ''

        # Parse color from '-- <color> --' pattern
        color = None
        color_match = re.search(r'--\s+(\d+)\s+--', orig_part)
        if color_match:
            color = int(color_match.group(1))

        # Parse orig_info: everything before the first '--'
        orig_info = orig_part.split('--')[0].strip()

        # Parse [line,col]path
        file_line = None
        file_path = None
        loc_match = loc_pattern.search(orig_part)
        if loc_match:
            file_line = int(loc_match.group(1))
            file_path = str(Path(loc_match.group(2)).resolve())

        entry = {
            'synth_node': synth_node,
            'synth_instance': synth_instance,
            'orig_info': orig_info,
        }
        if color is not None:
            entry['color'] = color
        if file_line is not None:
            entry['line'] = file_line
        if file_path is not None:
            entry['file_path'] = file_path

        mappings.append(entry)

    return {
        'mappings': mappings,
        'raw_output': stdout,
    }


def run_synalign(
    timing_report: str,
    netlist: str,
    liberty_file: str,
    lgshell_path: str,
    synth_top: str,
    orig_top: str,
    elab_top: str,
    standalone_files: list[str] | None = None,
    manifest_file: str | None = None,
    output_dir: str | None = None,
) -> dict:
    """
    Run the full synalign pipeline: create color.json, invoke lgshell, parse output.

    Returns:
        Parsed mapping dict from parse_synalign_output().
    """
    work_dir = Path(output_dir) if output_dir else Path('.')
    work_dir.mkdir(parents=True, exist_ok=True)

    # Extract critical path nodes from timing report and create color.json
    nodes = extract_nodes(timing_report)
    if not nodes:
        print('Warning: No nodes extracted from timing report', file=sys.stderr)
        return {'mappings': [], 'raw_output': ''}

    color_json_path = str(work_dir / 'color.json')
    create_color_json(synth_top, nodes, color_json_path)
    print(f'Created {color_json_path} with {len(nodes)} nodes', file=sys.stderr)

    # Build and run LiveHD lgshell command
    pipeline_cmd = build_lgshell_command(
        liberty_file=liberty_file,
        synth_top=synth_top,
        netlist_path=netlist,
        orig_top=orig_top,
        elab_top=elab_top,
        standalone_files=standalone_files,
        manifest_file=manifest_file,
        color_json=color_json_path,
    )

    cmd = [lgshell_path, pipeline_cmd]
    print('Running lgshell synalign...', file=sys.stderr)
    print(f"  Command: {lgshell_path} '{pipeline_cmd}'", file=sys.stderr)

    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=1800,
        )
    except FileNotFoundError:
        print(f'Error: lgshell not found at {lgshell_path}', file=sys.stderr)
        return {'mappings': [], 'raw_output': ''}
    except subprocess.TimeoutExpired:
        print('Error: lgshell timed out after 1800s', file=sys.stderr)
        return {'mappings': [], 'raw_output': ''}

    if result.returncode != 0:
        print(f'Warning: lgshell exited with code {result.returncode}', file=sys.stderr)
        if result.stderr:
            print(f'  stderr: {result.stderr[:500]}', file=sys.stderr)

    # Save filtered output (from marker onward) with absolute paths
    log_path = str(work_dir / 'synalign_output.log')
    loc_re = re.compile(r'(\[\s*\d+\s*,\s*\d+\s*\])((\.\./)*[^ \t\r\n]+)')
    filtered_lines = []
    found_marker = False
    for line in result.stdout.splitlines():
        if 'Reporting final critical resolved matches:' in line:
            found_marker = True
        if found_marker:

            def _absolutize(m):
                bracket = m.group(1)
                rel_path = m.group(2)
                abs_path = str(Path(rel_path).resolve())
                return bracket + abs_path

            line = loc_re.sub(_absolutize, line)
            filtered_lines.append(line)

    with open(log_path, 'w') as f:
        f.write('\n'.join(filtered_lines) + '\n')
    print(f'Saved filtered lgshell output to {log_path}', file=sys.stderr)

    # Parse SynAlign output
    parsed = parse_synalign_output(result.stdout)
    print(f'Parsed {len(parsed["mappings"])} net mappings', file=sys.stderr)

    return parsed


def main():
    parser = argparse.ArgumentParser(description='Run synalign via LiveHD lgshell')
    parser.add_argument('--timing-report', required=True, help='Path to STA timing report')
    parser.add_argument('--netlist', required=True, help='Path to synthesized netlist')
    parser.add_argument('--liberty', required=True, help='Path to liberty file')
    parser.add_argument('--lgshell', required=True, help='Path to lgshell binary')
    parser.add_argument('--synth-top', required=True, help='Synthesis top module name')
    parser.add_argument(
        '--orig-top',
        required=True,
        help='Original RTL synthesis target module. Use single quotes if value contains $ '
        "(e.g. --orig-top 'load_store_unit$cva6.ex_stage_i.lsu_i')",
    )
    parser.add_argument('--elab-top', required=True, help='Elaboration top module for original RTL (e.g. cva6)')
    parser.add_argument('--standalone-files', nargs='*', help='Standalone RTL files')
    parser.add_argument('--manifest-file', help='RTL manifest/filelist file')
    parser.add_argument('--output-dir', help='Output directory for color.json')

    args = parser.parse_args()

    result = run_synalign(
        timing_report=args.timing_report,
        netlist=args.netlist,
        liberty_file=args.liberty,
        lgshell_path=args.lgshell,
        synth_top=args.synth_top,
        orig_top=args.orig_top,
        elab_top=args.elab_top,
        standalone_files=args.standalone_files,
        manifest_file=args.manifest_file,
        output_dir=args.output_dir,
    )

    # Print structured output to stdout (parseable by caller)
    json.dump(result, sys.stdout, indent=2)
    print()


if __name__ == '__main__':
    main()
