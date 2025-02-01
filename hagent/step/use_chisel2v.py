# hagent/step/use_chisel2v.py

import argparse
import os
import re
import sys
import yaml
from hagent.tool.chisel2v import Chisel2v


def extract_module_name(chisel_code: str) -> str:
    """
    Extracts the module (class) name from the Chisel code.
    Assumes the module is defined as: class ModuleName extends Module
    """
    match = re.search(r'class\s+(\w+)\s+extends\s+Module', chisel_code)
    if match:
        return match.group(1)
    else:
        raise ValueError('Unable to find module name in Chisel code.')


def main():
    # Set up argument parsing
    parser = argparse.ArgumentParser(description='Convert Chisel code in a YAML file to Verilog using Chisel2v tool.')
    parser.add_argument('input_yaml', type=str, help='Path to the input YAML file.')
    parser.add_argument('output_yaml', type=str, help='Path to the output YAML file.')
    args = parser.parse_args()

    input_yaml_path = args.input_yaml
    output_yaml_path = args.output_yaml

    # Check if input file exists
    if not os.path.isfile(input_yaml_path):
        print(f"Error: Input YAML file '{input_yaml_path}' does not exist.", file=sys.stderr)
        sys.exit(1)

    # Read the input YAML file
    try:
        with open(input_yaml_path, 'r', encoding='utf-8') as f:
            yaml_data = yaml.safe_load(f)
    except Exception as e:
        print(f"Error reading YAML file '{input_yaml_path}': {e}", file=sys.stderr)
        sys.exit(1)

    # Ensure 'chisel_original' field exists
    if 'chisel_original' not in yaml_data or not yaml_data['chisel_original'].strip():
        print(f"Error: 'chisel_original' field is missing or empty in '{input_yaml_path}'.", file=sys.stderr)
        sys.exit(1)

    chisel_code = yaml_data['chisel_original']

    # Extract the module name from the Chisel code
    try:
        module_name = extract_module_name(chisel_code)
        print(f'Extracted module name: {module_name}')
    except ValueError as ve:
        print(f'Error: {ve}', file=sys.stderr)
        sys.exit(1)

    # Initialize Chisel2v and set it up
    chisel2v_tool = Chisel2v()
    if not chisel2v_tool.setup():
        print(f'Error setting up Chisel2v: {chisel2v_tool.error_message}', file=sys.stderr)
        sys.exit(1)
    print('Chisel2v setup successful.')

    # Generate Verilog
    try:
        verilog_output = chisel2v_tool.generate_verilog(chisel_code, module_name)
        print('Verilog generation successful.')
    except RuntimeError as re:
        print(f'Error during Verilog generation: {re}', file=sys.stderr)
        sys.exit(1)

    # Update the YAML data with the generated Verilog
    yaml_data['verilog_fixed'] = verilog_output

    # Write the updated YAML back to the output file
    try:
        with open(output_yaml_path, 'w', encoding='utf-8') as f:
            yaml.dump(yaml_data, f, sort_keys=False)
        print(f"Updated YAML written to '{output_yaml_path}'.")
    except Exception as e:
        print(f"Error writing to YAML file '{output_yaml_path}': {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
