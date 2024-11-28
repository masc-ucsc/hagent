# See LICENSE for details

import sys
import yaml
import datetime
import os

class Step:
    def __init__(self, test=None):
        if test is None:
            self.output_file, self.input_file = self.parse_arguments()

    def parse_arguments(self):
        output_file = None
        input_file = None

        args = sys.argv[1:]

        i = 0
        while i < len(args):
            if args[i].startswith("-o"):
                if args[i] == "-o":
                    i += 1
                    if i < len(args):
                        output_file = args[i]
                    else:
                        print("Error: Missing output file after -o")
                        sys.exit(1)
                else:
                    output_file = args[i][2:]
            elif not args[i].startswith("-"):
                input_file = args[i]
            i += 1

        if not output_file or not input_file:
            program_name = sys.argv[0]
            print(f"Usage: {program_name} -o<output_file> <input_file>")
            sys.exit(1)

        return output_file, input_file

    def read_input(self):
        data = {}
        try:
            with open(self.input_file, 'r') as f:
                data = yaml.safe_load(f)
        except Exception as e:
            return {
                'error': f"{sys.argv[0]} {datetime.datetime.now().isoformat()} - Error loading input file: {e}"
            }

        return data

    def write_output(self, data):
        def write_yaml_with_block_style(data, file):
            class LiteralStr(str):
                pass

            def represent_literal_str(dumper, value):
                return dumper.represent_scalar('tag:yaml.org,2002:str', value, style='|')

            def process_multiline_strings(obj):
                if isinstance(obj, dict):
                    return {k: process_multiline_strings(v) for k, v in obj.items()}
                elif isinstance(obj, list):
                    return [process_multiline_strings(i) for i in obj]
                elif isinstance(obj, str) and "\n" in obj:
                    return LiteralStr(obj)
                return obj

            yaml.add_representer(LiteralStr, represent_literal_str)
            processed_data = process_multiline_strings(data)
            yaml.dump(processed_data, file, default_flow_style=False, sort_keys=False)

        with open(self.output_file, 'w') as f:
            write_yaml_with_block_style(data, f)

    def run(self, data):
        # To be implemented in the subclass
        raise NotImplementedError("Subclasses should implement this!")

    def test(self, out_file, inp_file):
        self.input_file = os.path.join('tests', inp_file)
        expected_output_yaml = os.path.join('tests', out_file)
        expected_output = {}
        with open(expected_output_yaml, 'r') as f:
            expected_output = yaml.safe_load(f)

        input_data = self.read_input()
        result_data = self.run(input_data)
        assert result_data == expected_output

    def main(self):
        input_data = self.read_input()
        if 'error' in input_data:
            # Error occurred during reading input, write output_data as is
            print("WARNING: error field in input yaml, just propagating")
            self.write_output(input_data)
            return

        output_data = {}
        try:
            result_data = self.run(input_data)
            if result_data is None:
                result_data = {}
            # Propagate all fields from input to output unless overridden
            output_data.update(result_data)
        except Exception as e:
            # Handle exceptions during run
            output_data.update({
                'error': f"{sys.argv[0]} {datetime.datetime.now().isoformat()} - unable to write yaml: {e}"
            })
            print(f"ERROR: unable to write yaml: {e}")
        self.write_output(output_data)

