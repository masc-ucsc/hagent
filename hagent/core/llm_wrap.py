import os
import time
import datetime
import litellm
import sys
from typing import List, Dict

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

from hagent.core.llm_template import LLM_template
from hagent.inou.path_manager import PathManager


def dict_deep_merge(dict1: Dict, dict2: Dict) -> Dict:
    """Recursively merges dict2 into dict1, overwriting only leaf values.

    Args:
        dict1: The base dictionary (will be modified).
        dict2: The dictionary to merge into dict1.

    Returns:
        dict1 (modified).
    """
    for key, value in dict2.items():
        if key in dict1:
            if isinstance(dict1[key], dict) and isinstance(value, dict):
                dict_deep_merge(dict1[key], value)  # Recursive call for nested dicts
            else:
                dict1[key] = value  # Overwrite at leaf level
        else:
            dict1[key] = value  # Add new key-value pair
    return dict1


class LLM_wrap:
    """Wrapper for Large Language Model (LLM) interactions in HAgent.

    This class provides a standardized interface for LLM operations across HAgent,
    handling configuration, API calls, logging, cost tracking, and error management.
    Supports multiple LLM providers through the litellm library.

    Key features:
    - Configuration management through YAML files
    - Cost and token tracking across multiple calls
    - Comprehensive logging of all LLM interactions
    - Template-based prompt formatting
    - Environment variable validation for API keys
    - Disk-based caching for improved performance

    Attributes:
        name (str): Name/identifier for this LLM wrapper instance
        conf_file (str): Path to YAML configuration file
        log_file (str): Path to interaction log file
        last_error (str): Most recent error message
        chat_history (list): Message history for conversation-style interactions
        responses (list): Complete litellm response objects for tracing
        total_cost (float): Cumulative cost across all API calls
        total_tokens (int): Cumulative token usage
        total_time_ms (float): Cumulative time in milliseconds
        config (dict): Loaded configuration from YAML file
        llm_args (dict): LLM-specific arguments from config
    """

    def _load_config(self) -> Dict:
        """Load configuration from YAML file for this LLM wrapper instance.

        Performs case-insensitive lookup of configuration section by name.

        Returns:
            dict: Configuration dictionary for this LLM instance, empty dict on error
        """
        if not os.path.exists(self.conf_file):
            self._set_error(f'unable to read conf_file: {self.conf_file}')
            return {}

        try:
            yaml_loader = YAML(typ='safe')
            with open(self.conf_file, 'r', encoding='utf-8') as f:
                conf_data = yaml_loader.load(f)

            if not conf_data:
                return {}

            # Case-insensitive search for self.name
            lower_name = self.name.lower()
            config_name = next((k for k in conf_data if k.lower() == lower_name), None)
            if not config_name:
                return {}

            return conf_data[config_name]

        except Exception as e:
            self._set_error(f'reading conf_file: {e}')
            return {}

        return {}

    def _check_env_keys(self, model: str) -> bool:
        """Validate that required environment variables are set for the given model.

        Args:
            model: The model name/identifier (e.g., 'openai/gpt-4', 'anthropic/claude-3')

        Returns:
            bool: True if required environment variable is set

        Raises:
            ValueError: If required environment variable is missing
        """
        if model.startswith('fireworks'):
            required_key = 'FIREWORKS_AI_API_KEY'
        elif model.startswith('openai'):
            required_key = 'OPENAI_API_KEY'
        elif model.startswith('anthropic') or model.startswith('claude'):
            required_key = 'ANTHROPIC_API_KEY'
        elif model.startswith('replicate'):
            required_key = 'REPLICATE_API_KEY'
        elif model.startswith('cohere'):
            required_key = 'COHERE_API_KEY'
        elif model.startswith('together_ai'):
            required_key = 'TOGETHER_AI_API_KEY'
        elif model.startswith('openrouter'):
            required_key = 'OPENROUTER_API_KEY'
        elif model.startswith('ollama'):
            # Ollama access is achieved through a URL such as 'http://localhost:11434'
            required_key = 'OLLAMA_API_BASE'
        elif model.startswith('gemini'):
            # Gemini accepts either GEMINI_API_KEY or GOOGLE_API_KEY
            if os.environ.get('GEMINI_API_KEY') or os.environ.get('GOOGLE_API_KEY'):
                return True
            error_message = f"Error: Neither 'GEMINI_API_KEY' nor 'GOOGLE_API_KEY' is set for model '{model}'."
            print(error_message, file=sys.stderr)
            self._set_error(error_message)
            return False
        elif model.startswith('bedrock'):
            # AWS Bedrock requires both AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY
            if os.environ.get('AWS_ACCESS_KEY_ID') is None:
                error_message = f"Error: Environment variable 'AWS_ACCESS_KEY_ID' is not set for model '{model}'."
                print(error_message, file=sys.stderr)
                self._set_error(error_message)
                return False
            if os.environ.get('AWS_SECRET_ACCESS_KEY') is None:
                error_message = f"Error: Environment variable 'AWS_SECRET_ACCESS_KEY' is not set for model '{model}'."
                print(error_message, file=sys.stderr)
                self._set_error(error_message)
                return False
            return True
        # Add more providers as needed...
        else:
            # No specific key required for this model type (or you can raise an error if unknown)
            print(f'ERROR: No environment variable check defined for model: {model}', file=sys.stderr)
            return False

        if os.environ.get(required_key) is None:
            error_message = f"Error: Environment variable '{required_key}' is not set for model '{model}'."
            print(error_message, file=sys.stderr)  # Print to stderr
            self._set_error(error_message)
            return False

        return True

    def __init__(self, name: str, conf_file: str, log_file: str, overwrite_conf: Dict = {}):
        """Initialize LLM wrapper instance.

        Args:
            name: Identifier for this LLM wrapper instance (used for config lookup)
            conf_file: Path to YAML configuration file containing LLM settings
            log_file: Path to file for logging all LLM interactions
            overwrite_conf: Optional configuration overrides
        """
        self.name = name
        self.conf_file = conf_file
        self.log_file = PathManager().get_cache_path(log_file)

        self.last_error = ''
        self.chat_history = []  # Stores messages as [{"role": "...", "content": "..."}]
        self.responses = []  # Stores the complete litellm response for tracing LLM calls.
        self.total_cost = 0.0
        self.total_tokens = 0
        self.total_time_ms = 0.0

        # Initialize litellm cache (only if not already set)
        if not hasattr(litellm, 'cache') or litellm.cache is None:
            litellm.cache = litellm.Cache(type='disk')

        self.config = {}

        if os.path.exists(self.conf_file):
            self.config = self._load_config()
        elif self.conf_file:
            self._set_error(f'unable to read conf_file {conf_file}')
            return

        if overwrite_conf:
            self.config = dict_deep_merge(self.config, overwrite_conf)

        if 'llm' not in self.config:
            self._set_error(f'conf_file:{conf_file} or overwrite_conf must specify llm section')
            return

        self.llm_args = self.config['llm']

        if 'model' not in self.llm_args:
            self._set_error(f'conf_file:{conf_file} must specify llm "model" in section {name}')
            return

        # Override model with HAGENT_LLM_MODEL environment variable if set
        env_model = os.environ.get('HAGENT_LLM_MODEL')
        if env_model:
            # When overriding model, keep original parameters but enable drop_params
            # to automatically drop unsupported parameters instead of failing
            self.llm_args['model'] = env_model
            # Enable litellm to drop unsupported parameters instead of erroring
            # Note: This may reduce randomness for multiple outputs if temperature/top_p are dropped
            litellm.drop_params = True

        try:
            with open(self.log_file, 'a', encoding='utf-8'):
                pass
        except Exception as e:
            self._set_error(f'creating/opening log file: {e}')

    def _set_error(self, msg: str):
        self.last_error = msg
        print(msg, file=sys.stderr)

    def _log_event(self, event_type: str, data: Dict):
        def process_multiline_strings(obj):
            """
            Recursively convert strings with newlines into LiteralScalarString so that they
            are output in literal block style.
            """
            if isinstance(obj, dict):
                return {k: process_multiline_strings(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [process_multiline_strings(item) for item in obj]
            elif isinstance(obj, str) and '\n' in obj:
                # Wrap the multiline string so that ruamel.yaml outputs it using literal block style.
                return LiteralScalarString(obj)
            return obj

        def append_log(dt, file):
            # Process data to wrap multiline strings.
            processed_data = process_multiline_strings(dt)
            yaml = YAML()
            # Configure indentation (optional).
            yaml.indent(mapping=2, sequence=4, offset=2)
            yaml.dump(processed_data, file)

        entry = {
            'timestamp': datetime.datetime.now(datetime.UTC).isoformat(),  # include microseconds
            'type': event_type,
        }
        entry.update(data)
        try:
            with open(self.log_file, 'a', encoding='utf-8') as lf:
                append_log(entry, lf)
        except Exception as e:
            self._set_error(f'unable to log: {e}')

    def _messages_to_input(self, messages: List[Dict]) -> str:
        """Convert messages array to input string for responses API.

        Args:
            messages: List of message dicts with 'role' and 'content' keys

        Returns:
            str: Formatted input string
        """
        prompt_parts = []
        for msg in messages:
            role = msg.get('role', 'user')
            content = msg.get('content', '')
            if role == 'system':
                prompt_parts.append(f'System: {content}')
            elif role == 'user':
                prompt_parts.append(f'{content}')
            elif role == 'assistant':
                prompt_parts.append(f'Assistant: {content}')
        return '\n\n'.join(prompt_parts)

    def _call_llm(self, prompt_dict: Dict, prompt_index: str, n: int, max_history: int) -> List[str]:
        if self.last_error:
            return []

        start_time = time.time()

        template_dict = self.config.get(prompt_index, {})
        if not template_dict:
            if not self.conf_file:
                self._set_error(f'unable to find {prompt_index} entry in {self.config}')
            else:
                self._set_error(f'unable to find {prompt_index} entry in {self.conf_file}')
            return []

        template = LLM_template(template_dict)
        if template.last_error:
            self._set_error(f'template failed with {template.last_error}')
            return []

        # Format prompt
        try:
            formatted = template.format(prompt_dict)
            assert isinstance(formatted, list), 'Data should be a list'
        except Exception as e:
            self._set_error(f'template formatting error: {e}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:LLM_wrap.error', data=data)
            return []

        # Check if template returned error
        if 'error' in formatted:
            self._set_error(f'template returned error: {formatted["error"]}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:LLM_wrap.error', data=data)
            return []

        if max_history > 0:
            messages = self.chat_history[:max_history]
        else:
            messages = []
        messages += formatted

        # Convert messages to input string for responses API
        input_text = self._messages_to_input(messages)

        # Build llm_call_args for responses API
        llm_call_args = {}
        llm_call_args['model'] = self.llm_args.get('model', '')
        llm_call_args['input'] = input_text

        # Convert max_tokens to max_output_tokens for responses API
        if 'max_tokens' in self.llm_args:
            llm_call_args['max_output_tokens'] = self.llm_args['max_tokens']

        model = llm_call_args.get('model', '')

        # Anthropic models do not allow both temperature and top_p simultaneously
        anthropic_model = model.startswith('anthropic') or model.startswith('claude')

        # Copy other supported parameters
        for param in ['temperature', 'top_p', 'stream']:
            if param in self.llm_args:
                if anthropic_model and param == 'top_p':
                    continue  # Anthropic does not allow both temperature and top_p
                llm_call_args[param] = self.llm_args[param]
        if model == '':
            self._set_error('empty model name. No default model used')
            return []

        if not self._check_env_keys(model):
            self._set_error(f'environment keys not set for {model}')
            return []

        # Call litellm responses API
        try:
            start = time.time()

            # For better diversity when n > 1, make separate calls with varied parameters
            # This works for all models and ensures more diverse responses
            if n > 1:
                responses = []
                base_temperature = llm_call_args.get('temperature', 0.7)
                base_top_p = llm_call_args.get('top_p', 0.9)
                last_response = None  # Track only the last response for variation

                for i in range(n):
                    call_args = llm_call_args.copy()

                    # Scale temperature from 0 to 1 based on n, with one sample having default temperature
                    if n == 2:
                        # For n=2: use default temp and either 0 or 1
                        call_args['temperature'] = base_temperature if i == 0 else (0.0 if base_temperature > 0.5 else 1.0)
                    else:
                        # For n>2: distribute from 0 to 1, ensuring one sample has default temperature
                        mid_index = n // 2
                        if i == mid_index:
                            call_args['temperature'] = base_temperature  # Keep default for one sample
                        else:
                            # Scale others from 0 to 1
                            call_args['temperature'] = i / (n - 1)

                    # Scale top_p intelligently: vary around default with more diversity
                    # Skip top_p for Anthropic models (cannot use both temperature and top_p)
                    if not anthropic_model:
                        if n == 2:
                            call_args['top_p'] = base_top_p if i == 0 else max(0.1, min(1.0, 1.0 - base_top_p + 0.1))
                        else:
                            # For n>2: alternate between higher and lower values around default
                            if i == n // 2:
                                call_args['top_p'] = base_top_p  # Keep default for one sample
                            elif i % 2 == 0:
                                call_args['top_p'] = max(0.1, base_top_p - (i * 0.15))
                            else:
                                call_args['top_p'] = min(1.0, base_top_p + ((i - 1) * 0.15))

                    # Add variation to input to avoid caching when seeking diversity
                    if i > 0 and last_response:
                        # Truncate last response to 2KB if needed
                        prev_response = last_response
                        if len(prev_response) > 2048:
                            prev_response = prev_response[:2048] + '...'
                        call_args['input'] += (
                            f'\n\nThe last response answer was: """{prev_response}""" please try something different.'
                        )

                    r = litellm.responses(**call_args)
                    responses.append(r)

                    # Store only the last response for next iteration's variation
                    # Extract text from output[0].content[0].text
                    if hasattr(r, 'output') and r.output:
                        try:
                            last_response = r.output[0].content[0].text
                        except (IndexError, AttributeError):
                            pass

                # For responses API, we collect answers directly instead of combining choices
                answers = []
                total_tokens = 0
                total_cost = 0.0

                for resp in responses:
                    if hasattr(resp, 'output') and resp.output:
                        try:
                            text = resp.output[0].content[0].text
                            if text:
                                answers.append(text)
                        except (IndexError, AttributeError):
                            pass
                    if hasattr(resp, 'usage'):
                        total_tokens += getattr(resp.usage, 'total_tokens', 0)
                    try:
                        total_cost += litellm.completion_cost(completion_response=resp)
                    except Exception:
                        pass

                end = time.time()
                response = {'created': start, 'elapsed': end - start}
                tokens = total_tokens
                cost = total_cost
            else:
                r = litellm.responses(**llm_call_args)

                end = time.time()
                response = {'created': start, 'elapsed': end - start}

                # Extract answer from response
                answers = []
                if hasattr(r, 'output') and r.output:
                    try:
                        text = r.output[0].content[0].text
                        if text:
                            answers.append(text)
                    except (IndexError, AttributeError):
                        pass

                # Get tokens and cost
                tokens = 0
                if hasattr(r, 'usage'):
                    tokens = getattr(r.usage, 'total_tokens', 0)

                try:
                    cost = litellm.completion_cost(completion_response=r)
                except Exception:
                    cost = 0

        except Exception as e:
            self._set_error(f'litellm call error: {e}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:LLM_wrap.error', data=data)
            return []

        if cost == 0:
            # Simple proxy for https://fireworks.ai/pricing
            if 'deepseek-r1' in model:
                cost = 3.0 * tokens / 1e6
            else:
                cost = 0.9 * tokens / 1e6

        time_ms = (time.time() - start_time) * 1000.0
        self.total_cost += cost
        self.total_tokens += tokens
        self.total_time_ms += time_ms

        use_history = min(len(self.chat_history), max_history)
        event_type = f'{self.name}:LLM_wrap.inference with history={use_history}'

        data = {
            'model': model,
            'cost': cost,
            'tokens': tokens,
            'time_ms': time_ms,
            'prompt': formatted,
            'answers': answers,
        }

        if self.last_error:
            data['error'] = self.last_error

        self._log_event(event_type=event_type, data=data)

        response['cost'] = cost
        self.responses.append(response)
        return answers

    def _inference(self, prompt_dict: Dict, prompt_index: str, n: int = 1, max_history: int = 0) -> List[str]:
        """Perform LLM inference with the given prompt and parameters.

        Args:
            prompt_dict: Dictionary containing variables for prompt template substitution
            prompt_index: Name of the prompt template in the configuration file
            n: Number of completions to generate (default: 1)
            max_history: Maximum number of previous messages to include (default: 0)

        Returns:
            list: List of string responses from the LLM
        """
        answers = self._call_llm(prompt_dict, prompt_index, n=n, max_history=max_history)
        return answers

    def inference(self, prompt_dict: Dict, prompt_index: str, n: int = 1, max_history: int = 0) -> List[str]:
        """Public interface for LLM inference - delegates to _inference.

        Args:
            prompt_dict: Dictionary containing variables for prompt template substitution
            prompt_index: Name of the prompt template in the configuration file
            n: Number of completions to generate (default: 1)
            max_history: Maximum number of previous messages to include (default: 0)

        Returns:
            list: List of string responses from the LLM
        """
        return self._inference(prompt_dict, prompt_index, n, max_history)
