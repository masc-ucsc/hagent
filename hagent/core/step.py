# See LICENSE for details
# See LICENSE for details

import sys
import datetime
import os
import contextlib
import time

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

from hagent.core.llm_wrap import dict_deep_merge
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.tracer import Tracer, TracerMetaClass, s_to_us


def wrap_literals(obj):
    """Recursively wrap multiline strings as LiteralScalarString for nicer YAML output.

    Args:
        obj: The object to process - can be dict, list, string, or other types.

    Returns:
        The processed object with multiline strings wrapped as LiteralScalarString.
    """
    if isinstance(obj, dict):
        return {k: wrap_literals(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [wrap_literals(elem) for elem in obj]
    elif isinstance(obj, str) and '\n' in obj:
        return LiteralScalarString(obj)
    else:
        return obj


class Step(metaclass=TracerMetaClass):
    """Base class for all HAgent hermetic steps.

    Steps are the core building blocks of HAgent pipelines. Each step reads YAML input,
    performs a specific operation, and writes YAML output. Steps are designed to be
    hermetic (isolated) and can be run independently or chained together in pipelines.

    Key design principles:
    - YAML-centric: All input/output is in YAML format for debugging simplicity
    - Hermetic: Each step is isolated and can run independently
    - Traceable: Includes built-in tracing and performance monitoring
    - AI-integrated: Designed to work with LLM-based operations

    Attributes:
        input_file (str): Path to the input YAML file
        output_file (str): Path to the output YAML file
        overwrite_conf (dict): Configuration overrides
        setup_called (bool): Whether setup() has been called
        input_data (dict): Loaded input data from YAML file
    """

    def __init__(self):
        """Initialize a new Step with default values."""
        self.input_file = None
        self.output_file = None
        self.overwrite_conf = {}
        self.setup_called = False
        self.input_data = None

    def set_io(self, inp_file: str, out_file: str, overwrite_conf: dict = {}):
        """Set input/output files and configuration overrides.

        Args:
            inp_file: Path to the input YAML file
            out_file: Path to the output YAML file
            overwrite_conf: Dictionary of configuration values to override
        """
        self.input_file = inp_file
        self.output_file = out_file
        self.overwrite_conf = overwrite_conf

    def parse_arguments(self):
        """Parse command line arguments to set input and output files.

        Expected format: program.py -o output.yaml input.yaml

        Raises:
            SystemExit: If required arguments are missing or invalid
        """
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
        """Read and parse the input YAML file.

        Returns:
            dict: The parsed YAML data, or a dict with 'error' key if reading fails
        """
        if self.input_file is None:
            return {'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} - unset input_file (missing setup?):'}
        try:
            yaml_obj = YAML(typ='safe')
            with open(self.input_file, 'r') as f:
                data = yaml_obj.load(f)
        except Exception as e:
            return {'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} - Error loading input file: {e}'}

        return data

    def write_output(self, data):
        """Write data to the output YAML file.

        Args:
            data: Dictionary to write as YAML output
        """
        yaml_obj = YAML()
        yaml_obj.default_flow_style = False
        processed_data = wrap_literals(data)
        with open(self.output_file, 'w') as f:
            yaml_obj.dump(processed_data, f)

    @contextlib.contextmanager
    def temporary_env_vars(self):
        """
        Context manager to temporarily set environment variables from input_data.
        Expected format in YAML:
          set_env_vars:
            POTATO: "foo"
            ANOTHER_VAR: "another_value"
        Alternatively, if provided as a list with a single mapping, the mapping is used.
        """
        env_vars = self.input_data.get('set_env_vars', {})

        original_env = {}
        try:
            for key, value in env_vars.items():
                original_env[key] = os.environ.get(key)
                os.environ[key] = value  # Set temporary environment variable
            yield
        finally:
            for key in env_vars.keys():
                if original_env.get(key) is None:
                    os.environ.pop(key, None)  # Unset if it did not exist originally
                else:
                    os.environ[key] = original_env[key]  # Restore original value

    def setup(self):
        """Set up the step by loading input data and validating configuration.

        Must be called after parse_arguments() or set_io() and before run().
        Loads input YAML, validates environment variables, and applies overrides.

        Raises:
            SystemExit: If input contains errors or setup validation fails
        """
        self.setup_called = True
        if self.output_file is None:
            self.error('must call parse_arguments or set_io before setup')

        if self.input_file:
            self.input_data = self.read_input()
            env_vars = self.input_data.get('set_env_vars', {})
            if env_vars and not isinstance(env_vars, dict):
                self.error('set_env_vars must be a map in yaml')
                return

            if isinstance(self.input_data, dict) and 'error' in self.input_data:
                # Propagate error from input reading and exit
                print('WARNING: error field in input yaml, just propagating')
                self.write_output(self.input_data)
                sys.exit(4)
            if self.overwrite_conf:
                self.input_data = dict_deep_merge(self.input_data, self.overwrite_conf)
        else:
            self.input_data = self.overwrite_conf

    def run(self, data):
        """Execute the step's main logic.

        This is the core method that subclasses must implement to define
        their specific behavior. Takes input data and returns output data.

        Args:
            data: Input data dictionary loaded from YAML

        Returns:
            dict: Output data to be written to YAML

        Raises:
            NotImplementedError: Must be implemented by subclasses
        """
        raise NotImplementedError('Subclasses should implement this!')

    def test(self, exp_file):
        # Unit test that compares run output against an expected YAML file.
        yaml_obj = YAML(typ='safe')
        with open(exp_file, 'r') as f:
            expected_output = yaml_obj.load(f)
        assert expected_output is not None
        assert expected_output != {}

        self.input_data = self.read_input()
        self.setup()
        with self.temporary_env_vars():
            result_data = self.run(self.input_data)
        if result_data != expected_output:
            print(f'input_data: {self.input_data}')
            print(f'result_data: {result_data}')
            print(f'expect_data: {expected_output}')
        assert result_data == expected_output

    def error(self, msg: str):
        """Handle step errors by logging and writing error output.

        Args:
            msg: Error message to log and write

        Raises:
            ValueError: Always raises with the error message
        """
        output_data = self.input_data.copy() if self.input_data else {}
        output_data.update({'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} {msg}'})
        print(f'ERROR: {sys.argv[0]} : {msg}')
        self.write_output(output_data)
        raise ValueError(msg)

    def augment_output_data(self, output_data: dict, start: float, elapsed: float, history: list):
        output_data['step'] = self.__class__.__name__
        output_data['tracing'] = {}
        output_data['tracing']['start'] = s_to_us(start)
        output_data['tracing']['elapsed'] = s_to_us(elapsed)
        # Ensure that "input" is a list for future multi-input support
        # Store paths relative to where the script was called.
        input = self.input_file
        if isinstance(self.input_file, str):
            input = [self.input_file]
        output_data['tracing']['input'] = input
        output_data['tracing']['output'] = self.output_file
        output_data['tracing']['trace_events'] = Tracer.get_events()
        output_data['tracing']['history'] = history

    def step(self):
        """Execute the complete step workflow with tracing and error handling.

        This is the main entry point that orchestrates the step execution:
        1. Validates setup has been called
        2. Executes run() with temporary environment variables
        3. Collects LLM costs and tokens from any attached LLM_wrap instances
        4. Adds tracing information
        5. Writes output YAML file

        Returns:
            dict: The complete output data written to YAML file

        Raises:
            NotImplementedError: If setup() has not been called first
        """
        if not self.setup_called:
            raise NotImplementedError('must call setup before step')
        start = time.time()
        output_data = {}
        try:
            # Set environment variables temporarily before running.
            with self.temporary_env_vars():
                result_data = self.run(self.input_data)
            if result_data is None:
                result_data = {}
            # Propagate all fields from input to output unless overridden.
            output_data.update(result_data)
        except Exception as e:
            output_data.update({'error': f'{sys.argv[0]} {datetime.datetime.now().isoformat()} - unable to write yaml: {e}'})
            print(f'ERROR: unable to write yaml: {e}')

        # Get total cost and tokens if there is any LLM attached
        # Also get the chat history to dump any relevant stats in the yaml.
        cost = 0.0
        tokens = 0
        history = []
        for attr_name in dir(self):
            try:
                attr_value = getattr(self, attr_name)
                if isinstance(attr_value, LLM_wrap):
                    cost += attr_value.total_cost
                    tokens += attr_value.total_tokens
                    history = attr_value.responses
            except AttributeError:
                # Skip attributes that can't be accessed
                pass
        if cost > 0:
            cost += output_data.get('cost', 0.0)
            output_data['cost'] = cost

        if tokens > 0:
            tokens += output_data.get('tokens', 0)
            output_data['tokens'] = tokens

        elapsed = time.time() - start
        # Ensure that all relevant tracing attributes are accurate for this Step.
        self.augment_output_data(output_data, start, elapsed, history)
        self.write_output(output_data)
        return output_data
