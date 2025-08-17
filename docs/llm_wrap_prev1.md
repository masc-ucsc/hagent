
The llm_wrap is a Python class that wraps around llmlite with the following characteristics:

* It provides a wrapper around llmlite to call LLMs which build a chat history.

* It enables llmlite disk cache
```
  litellm.cache = Cache(type="disk")
```

* The main API is:
    * clear_history(): Clears the chat history
    * chat(prompt_dict:Dict): Calls llmlite with the llm_template provided at initialization. Returns a string with the chat answer.
    * inference(prompt_dict:Dict): Same as 'chat', but does not add to the chat history

* All transactions are added to the log yaml file. The log file is passed at initialization. Each call adds to the 'llm_wrap_log' entry in the yaml file.

* It tracks the 'cost' and total number of 'tokens' (chat and inference)

* The cost and tokens also added to the log file ('llm_wrap_tokens' and 'llm_wrap_cost' yaml arrays)

