import os
import time
import datetime
import litellm
import sys
from typing import List, Dict

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString

from hagent.core.llm_template import LLM_template
from hagent.inou.output_manager import get_output_path


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
        elif model.startswith('anthropic'):
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
        self.log_file = get_output_path(log_file)

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

    def _call_openai_responses_api(self, messages, model, n, llm_args):
        """Call OpenAI's Responses API directly for gpt-5-codex and similar models.

        litellm doesn't support the Responses API yet, so we use the OpenAI SDK directly.
        """
        try:
            from openai import OpenAI
        except ImportError:
            self._set_error('openai package required for gpt-5-codex (Responses API)')
            return []

        import time

        # Extract model name without provider prefix
        model_name = model.replace('openai/', '')

        # Create OpenAI client
        client = OpenAI(api_key=os.environ.get('OPENAI_API_KEY'))

        # Convert messages format (litellm format to OpenAI format)
        # The Responses API expects 'input' parameter instead of 'messages'
        # For now, concatenate messages into a single prompt
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

        input_text = '\n\n'.join(prompt_parts)

        # Call Responses API
        start = time.time()
        try:
            # Note: The Responses API uses different parameters than Chat Completions
            # - Uses 'input' instead of 'messages'
            # - Uses 'max_output_tokens' instead of 'max_tokens'
            # - Does NOT support temperature, top_p, presence_penalty, frequency_penalty for reasoning models

            # Reasoning models need more tokens for internal reasoning + output
            # These models often timeout with default 2048 tokens
            # Use moderate values - too many tokens can cause "overthinking"
            if 'o3-mini' in model_name.lower():
                default_tokens = 16384  # 16k for o3-mini (moderate, prevents overthinking)
            elif 'o3' in model_name.lower():
                default_tokens = 32768  # 32k for o3 (full version)
            elif 'gpt-5-codex' in model_name.lower() or 'codex' in model_name.lower():
                default_tokens = 16384  # 16k for gpt-5-codex (moderate, was causing issues at 64k)
            else:
                default_tokens = 16384  # 16k default for other reasoning models

            max_tokens = llm_args.get('max_tokens', default_tokens)
            print(f'[LLM_wrap] Detected Responses API model: {model}')
            print(f'[LLM_wrap DEBUG] max_output_tokens: {max_tokens}')
            print(f'[LLM_wrap DEBUG] input_text length: {len(input_text)} chars')
            print(f'[LLM_wrap DEBUG] First 300 chars of input: {input_text[:300]}')

            # Make the API call
            print(f'[LLM_wrap DEBUG] Calling API with model: {model_name}')
            response = client.responses.create(
                model=model_name,
                input=input_text,
                max_output_tokens=max_tokens,
            )

            # For reasoning models, we need to POLL until completion
            # The initial response has status='incomplete' and we need to wait
            response_id = response.id
            print(f'[LLM_wrap] Response ID: {response_id}')
            print(f'[LLM_wrap] Initial status: {response.status if hasattr(response, "status") else "unknown"}')

            # Poll until reasoning is complete
            max_poll_time = 600  # 10 minutes max
            poll_interval = 5  # Check every 5 seconds
            elapsed = 0

            while hasattr(response, 'status') and response.status == 'incomplete':
                if elapsed >= max_poll_time:
                    self._set_error(f'Responses API timeout after {max_poll_time}s - response still incomplete')
                    return []

                print(f'[LLM_wrap] Reasoning in progress... (elapsed: {elapsed}s)')
                time.sleep(poll_interval)
                elapsed += poll_interval

                # Retrieve the updated response
                response = client.responses.retrieve(response_id)

            end = time.time()
            print(f'[LLM_wrap] Response completed in {end - start:.1f}s')
            print(f'[LLM_wrap] Final status: {response.status if hasattr(response, "status") else "unknown"}')

            # DEBUG: Print raw response structure
            print(f'[LLM_wrap DEBUG] Response type: {type(response)}')
            if hasattr(response, 'error') and response.error:
                print(f'[LLM_wrap DEBUG] response.error: {response.error}')
            if hasattr(response, 'output_text'):
                print(f'[LLM_wrap DEBUG] response.output_text length: {len(response.output_text)} chars')
                print(f'[LLM_wrap DEBUG] response.output_text preview: {repr(response.output_text)[:300]}')

            if hasattr(response, 'output'):
                print(f'[LLM_wrap DEBUG] response.output type: {type(response.output)}')
                print(f'[LLM_wrap DEBUG] response.output length: {len(response.output)} items')
            else:
                print('[LLM_wrap DEBUG] response has NO output attribute!')

            # Convert OpenAI Responses API response to format compatible with our code
            # The Responses API uses 'output_text' field instead of 'choices'
            answers = []
            cost = 0.0
            tokens = 0

            # Prepare log data structure
            log_data = {
                'model': model,
                'api': 'responses',
                'input': input_text[:500] + '...' if len(input_text) > 500 else input_text,
            }

            # Extract text from response using output_text property
            # The output_text property automatically aggregates all output_text items from the output list
            response_text = None
            extraction_method = None

            if hasattr(response, 'output_text'):
                response_text = response.output_text
                extraction_method = 'output_text'

                # If output_text is empty but output exists, use comprehensive fallback extraction
                # This restores the robust logic that worked on 11/02-11/08
                if not response_text and hasattr(response, 'output'):
                    output = response.output

                    # Try direct string
                    if isinstance(output, str):
                        response_text = output
                        extraction_method = 'output (string)'
                    # Try output.content
                    elif hasattr(output, 'content'):
                        content = output.content
                        if isinstance(content, list) and len(content) > 0:
                            if hasattr(content[0], 'text'):
                                response_text = content[0].text
                                extraction_method = 'output.content[0].text'
                            else:
                                response_text = str(content[0])
                                extraction_method = 'output.content[0] (str)'
                        elif isinstance(content, str):
                            response_text = content
                            extraction_method = 'output.content (string)'
                        else:
                            response_text = str(content)
                            extraction_method = 'output.content (fallback)'
                    # Try output.text
                    elif hasattr(output, 'text'):
                        response_text = output.text
                        extraction_method = 'output.text'
                    # Try output as list
                    elif isinstance(output, list) and len(output) > 0:
                        # Sometimes output is a list of message objects
                        if hasattr(output[0], 'content'):
                            content = output[0].content
                            if isinstance(content, list) and len(content) > 0:
                                if hasattr(content[0], 'text'):
                                    response_text = content[0].text
                                    extraction_method = 'output[0].content[0].text'
                                else:
                                    response_text = str(content[0])
                                    extraction_method = 'output[0].content[0] (str)'
                            elif isinstance(content, str):
                                response_text = content
                                extraction_method = 'output[0].content (string)'
                            else:
                                response_text = str(content)
                                extraction_method = 'output[0].content (fallback)'
                        elif hasattr(output[0], 'text'):
                            response_text = output[0].text
                            extraction_method = 'output[0].text'

            elif hasattr(response, 'choices') and response.choices:
                # Fallback to choices structure (for compatibility with older API versions)
                for choice in response.choices:
                    if hasattr(choice, 'message') and hasattr(choice.message, 'content'):
                        response_text = choice.message.content
                        extraction_method = 'choices[].message.content'
                        break

            # DEBUG: Print what we extracted
            print(f'[LLM_wrap DEBUG] response_text type: {type(response_text)}')
            print(f'[LLM_wrap DEBUG] response_text value: {repr(response_text)[:200]}')
            print(f'[LLM_wrap DEBUG] extraction_method: {extraction_method}')

            # Check if we extracted text (use 'is not None' to handle empty strings)
            if response_text is not None and len(response_text) > 0:
                answers.append(response_text)
                log_data['extraction_method'] = extraction_method
                log_data['response_length'] = len(response_text)
            elif response_text is not None and len(response_text) == 0:
                log_data['warning'] = 'Response text was empty string'
                log_data['extraction_method'] = extraction_method
                self._set_error('Responses API returned empty text')
            else:
                # Log the actual response structure for debugging
                print('[LLM_wrap DEBUG] Failed to extract text!')
                print(f'[LLM_wrap DEBUG] response type: {type(response)}')
                print(f'[LLM_wrap DEBUG] response attrs: {[attr for attr in dir(response) if not attr.startswith("_")][:20]}')
                if hasattr(response, 'output'):
                    print(f'[LLM_wrap DEBUG] response.output: {response.output}')
                log_data['error'] = 'Could not extract text from response'
                log_data['response_type'] = str(type(response))
                log_data['response_attrs'] = [attr for attr in dir(response) if not attr.startswith('_')][:20]
                self._set_error(f'Responses API returned data but could not extract text. Type: {type(response)}')

            # Calculate cost (GPT-5-Codex pricing: $1.25/M input, $10/M output)
            if hasattr(response, 'usage'):
                usage = response.usage
                input_tokens = getattr(usage, 'prompt_tokens', 0)
                output_tokens = getattr(usage, 'completion_tokens', 0)
                tokens = input_tokens + output_tokens
                cost = (input_tokens / 1_000_000 * 1.25) + (output_tokens / 1_000_000 * 10.0)

            # Update tracking
            self.total_tokens += tokens
            self.total_cost += cost
            self.total_time_ms += (end - start) * 1000

            # Add final data to log
            log_data.update(
                {
                    'answers': answers,
                    'tokens': tokens,
                    'cost': cost,
                    'elapsed_ms': (end - start) * 1000,
                }
            )
            self._log_event(event_type=f'{self.name}:openai_responses_api', data=log_data)

            return answers

        except Exception as e:
            self._set_error(f'OpenAI Responses API error: {e}')
            self._log_event(event_type=f'{self.name}:openai_responses_api.error', data={'error': str(e)})
            return []

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

        # For inference, messages might just be what we got. For chat, this is final messages to send.
        llm_call_args = {}
        llm_call_args.update(self.llm_args)
        llm_call_args['messages'] = messages
        llm_call_args['n'] = n

        model = llm_call_args.get('model', '')
        if model == '':
            self._set_error('empty model name. No default model used')
            return []

        if not self._check_env_keys(model):
            self._set_error(f'environment keys not set for {model}')
            return []

        # Detect if model requires Responses API instead of Chat Completions API
        # These models use OpenAI's newer Responses API endpoint
        responses_api_keywords = ['gpt-5-codex', 'gpt-5', 'o3-mini', 'o3', 'o1-mini', 'o1-preview', 'o1']
        use_responses_api = any(keyword in model.lower() for keyword in responses_api_keywords)

        # Use OpenAI SDK directly for Responses API models since litellm doesn't support it yet
        if use_responses_api:
            print(f'[LLM_wrap] Detected Responses API model: {model}')
            return self._call_openai_responses_api(messages, model, n, llm_call_args)

        # Call litellm
        try:
            start = time.time()

            # For better diversity when n > 1, make separate calls with varied parameters
            # This works for all models and ensures more diverse responses
            if n > 1:
                # Remove 'n' parameter and make multiple calls with varied parameters for diversity
                varied_args = llm_call_args.copy()
                varied_args.pop('n', None)

                responses = []
                base_temperature = varied_args.get('temperature', 0.7)
                base_top_p = varied_args.get('top_p', 0.9)
                last_response = None  # Track only the last response for variation

                for i in range(n):
                    call_args = varied_args.copy()

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

                    # Copy messages and add variation to avoid caching when seeking diversity
                    call_args['messages'] = [msg.copy() for msg in call_args['messages']]

                    if i > 0 and last_response and call_args['messages']:
                        last_msg = call_args['messages'][-1]
                        if last_msg.get('role') == 'user':
                            # Truncate last response to 2KB if needed
                            prev_response = last_response
                            if len(prev_response) > 2048:
                                prev_response = prev_response[:2048] + '...'
                            last_msg['content'] += (
                                f'\n\nThe last response answer was: """{prev_response}""" please try something different.'
                            )

                    # Call litellm completion (Responses API models handled separately above)
                    r = litellm.completion(**call_args)
                    responses.append(r)

                    # Store only the last response for next iteration's variation
                    if r and 'choices' in r and r['choices']:
                        last_response = r['choices'][0]['message']['content']

                # Combine responses
                combined_choices = []
                for resp in responses:
                    combined_choices.extend(resp['choices'])

                # Use the first response as template and replace choices
                r = responses[0]
                # Convert to dict first since ModelResponse doesn't support item assignment
                r_dict = r.to_dict()
                r_dict['choices'] = combined_choices
                # Convert back to ModelResponse-like object for consistency
                r = litellm.ModelResponse(**r_dict)
            else:
                # Call litellm completion (Responses API models handled separately above)
                r = litellm.completion(**llm_call_args)

            end = time.time()
            # Augment the litellm.ModelResponse with duration.
            response = r.to_dict()
            # Overwrite the response 'created' time to get matching sub-second accuracy.
            response['created'] = start
            response['elapsed'] = end - start
        except Exception as e:
            self._set_error(f'litellm call error: {e}')
            data = {'error': self.last_error}
            self._log_event(event_type=f'{self.name}:LLM_wrap.error', data=data)
            return []

        answers = []
        cost = 0.0
        tokens = 0
        try:
            cost = litellm.completion_cost(completion_response=r)
        except Exception:
            cost = 0  # Model may not be updated for cost

        if cost == 0:
            # Simple proxy for https://fireworks.ai/pricing
            if 'deepseek-r1' in model:
                cost = 3.0 * tokens / 1e6
            else:
                cost = 0.9 * tokens / 1e6

        try:
            for c in r['choices']:
                answers.append(c['message']['content'])

            usage = r['usage']
            tokens += usage.get('total_tokens', 0)
        except Exception as e:
            self._set_error(f'parsing litellm response error: {e}')

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
