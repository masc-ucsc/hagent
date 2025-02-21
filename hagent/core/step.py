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
        def debug_data(obj, indent=0):
            prefix = " " * indent
            if isinstance(obj, dict):
                for k, v in obj.items():
                    print(f"{prefix}Key: {repr(k)} (type: {type(k)})")
                    debug_data(v, indent+2)
            elif isinstance(obj, list):
                for i, item in enumerate(obj):
                    print(f"{prefix}[{i}]: (type: {type(item)})")
                    debug_data(item, indent+2)
            else:
                print(f"{prefix}Value: {repr(obj)} (type: {type(obj)})")
    
        print("DEBUG: Raw output data before processing:")
        debug_data(data)
    
        def write_yaml_with_block_style(data, file):
            def process_obj(obj):
                if isinstance(obj, dict):
                    return {str(k): process_obj(v) for k, v in obj.items()}
                elif isinstance(obj, list):
                    return [process_obj(i) for i in obj]
                # If the object has a __dict__, use its dictionary.
                elif hasattr(obj, '__dict__'):
                    return process_obj(vars(obj))
                elif isinstance(obj, (str, int, float, bool)) or obj is None:
                    return obj
                else:
                    return str(obj)
            processed_data = process_obj(data)
            
            print("DEBUG: Processed data for YAML dumping:")
            debug_data(processed_data)
            
            try:
                yaml.safe_dump(processed_data, file, default_flow_style=False, sort_keys=False)
            except Exception as e:
                print("Error dumping YAML with processed_data:")
                print(processed_data)
                raise e
    
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
