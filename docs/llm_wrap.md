
**Class Name:** `llm_wrap`

**Purpose:** A Python class that wraps around the `litellm` library to provide
a simplified interface for interacting with Large Language Models (LLMs),
including chat history management, logging, and cost/token tracking.

**Initialization Parameters:**

*   `name`: (string) Pass name used for loging and reading configuration.
*   `conf_file`: (string) path to yaml file with llm_wrap configuration.
*   `log_file`: (string) Path to a YAML file where the class will log all interactions and tracking information.
*   `init_template`: (LLM_template instance). LLM_template called when there is no history (first chat call or inference call).
*   `chat_template`: (LLM_template instance). Template called for `chat` when history exists (not the first chat call).

Example LLM_template use where `d` is the returns a dictionary that has
replaced `xx` for `potato` in all the cases. If LLM_template detects an error,
a dictionary with `error` field is returned.
```
    assert isinstance(init_or_chat_template, LLM_template)
    d = init_or_chat_template.format({"xx": "potato"})
    assert isinstance(d, dict)
```

**Core Functionality:**

1.  **LLM Interaction:**
    *   Enables `litellm` disk caching:
        ```python
        import litellm
        from litellm import Cache
        litellm.cache = Cache(type="disk")
        ```
2.  **Chat History Management:**
    *   Maintains an internal chat history used when calling litellm.

3.  **Logging:**
    *   Logs all interactions (chats and inferences) to a YAML file specified during initialization.
    *   It appends to the YAML log file.
    *   Each interaction is appended to the `llm_wrap`. The entry includes the `prompt` (`str`) and `answers` (`List[str]`) use in the litellm call, but also the query `cost`, `tokens`, and `time_ms` used. `cost` and `tokens` can be extracted from litellm, and they are just single numbers added for each call. `time_ms` is the total time spend in the method call which should include litellm, template formatting and any other python work.
    *   The logging has to be careful because other threads can be adding to the same yaml log at the same time. The log file should be open with append mode. Something like `open(log_file, "a", encoding="utf-8")` should work.

4.  **Total Statistics Tracking:**
    *   The class also tracks the total `cost`, `tokens`, and `time_ms` for both `chat` and `inference`.

**API:**

*   **`__init__(self, name:str, conf_file: str, log_file: str, init_template: LLM_template, chat_template: LLM_template)`:**
    *   Initializes the `llm_wrap` object.
    *   Sets up `litellm` with disk caching.
    *   Uses the conf_file `name.llm_wrap` dictionary as llm_lite initialization arguments, using llm_lite default values otherwise.
    *   Initializes internal variables for chat history, cost, and token tracking.
    *   No exception is raised on failures like missing log file or incorect llmlie settings. It will return empty strings for `chat` and `inference` calls, and if the log file can be created it will add an `error` field with the reason for the error. The same error is set to `last_error`.
    *   If template returns a dictionary with the `error` field, it means that if failed. Notify in the log that there was an `error` in the template format call.
    *   Opens or creates the log file.

*   **`clear_history(self)`:**
    *   Clears the internal chat history.
    *   Updates the log file to reflect the cleared history. In the log yaml file, a new entry in `llm_wrap` should indicated `clear_history` as `True`

*   **`chat(self, prompt_dict: Dict) -> str`:**
    *   Sends a prompt to the LLM (using `litellm`)
    *   Uses the `llm_template` provided at initialization to create the `litellm` dictionary argument call.
    *   Adds the prompt and the LLM's answer to the internal chat history.
    *   Returns the LLM's answer as a string.
    *   Logs the interaction (prompt, answers, cost, and tokens) to the YAML file. Notice, it uses `answers` with only one entry to be consistent with the `inference` call.
    *   Updates the total cost and token count.
    *   In any failure case, it returns an empty string and if possible logs the reason in the log YAML file.

*   **`inference(self, prompt_dict: Dict, n: int = 1) -> List[str]`:**
    *   Similar to `chat` **except** the following:
    *   It does not add the prompt and answer to the internal chat history.
    *   It still does log the interaction, cost, and tokens as in the `chat` method.
    *   If `n` is provided litellm can return multiple answers.

*  **`last_error -> str`:**
    *   String with the last error that LLM_wrap had. It is cleared if chat/inference works without error.

**Example Usage (Illustrative):**

```python
wrapper = llm_wrap(log_file="log.yaml", conf="conf.yaml"...)

response1 = wrapper.chat({"user": "What is the capital of France?"})
print(response1)

response2 = wrapper.inference({"user": "What is the meaning of life?"})
print(response2)

wrapper.clear_history()

# ... inspect log.yaml to see logged interactions, cost, and tokens ...
```

**Log File Structure Example:**

`some_name` is whatever name is passed to LLM_wrap initialization.

```yaml
- timestamp: 2023-10-27 10:00:00
  type: some_name:llm_wrap.chat  # or 'inference'
  model: gpt-3.5-turbo # or the model specified in conf.yaml
  prompt: "You are a 5 year old. What is the capital of France?"  # text generated from llm_template and chat arguments
  answers:
    - "The capital of France is Paris."
  cost: 0.002
  tokens: 20
  time_ms: 300
- timestamp: 2023-10-27 10:05:00
  type: some_name:llm_wrap.inference
  model: gpt-3.5-turbo
  prompt: "You are a 5 year old. What is the meaning of life?"  # text generated from llm_template and chat arguments
  answers:
    - "The meaning of life is a philosophical question..."
    - "Not easy..." # if n==2 in the call
  cost: 0.003
  tokens: 30
- timestamp: 2023-10-27 10:15:00
  type: some_name:llm_wrap.clear_history
- timestamp: 2024-10-27 10:15:00
  type: zzz:some_other_module.some_method
  whatever: 300
```
**Conf Structure Example:**

`some_name` matches the LLM_wrap initialization name. It only uses fields that may exist in the `some_name` `llm_wrap` subfield.

```yaml
some_name:
  llm_wrap:
    model: "gpt-4"
    temperature: 0.7
    top_p: 0.9
  max_retries: 3
  other_field: "xxx"
other_name:
  llm_wrap:
    model: "gpt-3"
    seed: 330
    top_p: 0.9
  other_field: "zzz"

