# See LICENSE for details

import sys
import yaml
import datetime

from hagent.core.llm_wrap import dict_deep_merge

class Step:
    def __init__(self):
        self.input_file = None
        self.output_file = None
        self.setup_called = False

    def set_io(self, inp_file: str, out_file: str, overwrite_conf: dict={}):
        self.input_file = inp_file
        self.output_file = out_file
        self.overwrite_conf = overwrite_conf

    def parse_arguments(self):
        self.input_file = None
        self.output_file = None

        args = sys.argv[1:]

        i = 0
        while i < len(args):
            if args[i].startswith('-o'):
                if args[i] == '-o':
                    i += 1
                    if i < len(args):
                        self.output_file = args[i]
                    else:
                        print('Error: Missing output file after -o')
                        sys.exit(1)
                else:
                    self.output_file = args[i][2:]
            elif not args[i].startswith('-'):
                self.input_file = args[i]
            i += 1

        if self.output_file is None or self.input_file is None:
            program_name = sys.argv[0]
            print(f'Usage: {program_name} -o<output_yaml_file> <input_yaml_file>')
            sys.exit(1)

    def read_input(self):
        data = {}
        if self.input_file is None:
            return {'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} - unset input_file (missing setup?):'}

        try:
            with open(self.input_file, 'r') as f:
                data = yaml.safe_load(f)
        except Exception as e:
            return {'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} - Error loading input file: {e}'}

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
                elif isinstance(obj, str) and '\n' in obj:
                    return LiteralStr(obj)
                return obj

            yaml.add_representer(LiteralStr, represent_literal_str)
            processed_data = process_multiline_strings(data)
            yaml.dump(processed_data, file, default_flow_style=False, sort_keys=False)

        with open(self.output_file, 'w') as f:
            write_yaml_with_block_style(data, f)

    def setup(self):
        self.setup_called = True
        if self.output_file is None:
            self.error('must call parse_arguments or set_io before setup')

        if self.input_file:
            self.input_data = self.read_input()
            if 'error' in self.input_data:
                # Error occurred during reading input, write output_data as is
                print('WARNING: error field in input yaml, just propagating')
                self.write_output(self.input_data)
                exit(4)
            if self.overwrite_conf:
                self.input_data = dict_deep_merge(self.input_data, self.overwrite_conf)
        else:
            self.input_data = self.overwrite_conf

    def run(self, data):
        # To be implemented in the subclass
        raise NotImplementedError('Subclasses should implement this!')

    def test(self, exp_file):
        expected_output_yaml = exp_file
        expected_output = {}
        with open(expected_output_yaml, 'r') as f:
            expected_output = yaml.safe_load(f)

        assert expected_output is not None
        assert expected_output != {}

        self.input_data = self.read_input()
        self.setup()
        result_data = self.run(self.input_data)
        if result_data != expected_output:
            print(f'input_data:{self.input_data}')
            print(f'result_data:{result_data}')
            print(f'expect_data:{expected_output}')

        assert result_data == expected_output

    def error(self, msg: str):
        if self.input_data is None:
            output_data = {}
        else:
            output_data = self.input_data.copy()

        output_data.update({'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} {msg}'})
        print(f'ERROR: {sys.argv[0]} : {msg}')
        self.write_output(self.input_data)
        raise ValueError(msg)

    def step(self):
        if not self.setup_called:
            raise NotImplementedError('must call setup before step')

        output_data = {}
        try:
            result_data = self.run(self.input_data)
            if result_data is None:
                result_data = {}
            # Propagate all fields from input to output unless overridden
            output_data.update(result_data)
        except Exception as e:
            # Handle exceptions during run
            output_data.update({'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} - unable to write yaml: {e}'})
            print(f'ERROR: unable to write yaml: {e}')
        self.write_output(output_data)

        return output_data
