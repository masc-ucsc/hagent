# List of tested models

Use HAGENT_LLM_MODEL to overwrite the default models in configurations.

## Bedrock models

For AWS/bedrock, you need:

```
export AWS_ACCESS_KEY_ID=....
export AWS_SECRET_ACCESS_KEY=....
```

For llama3.3 70B:
```
export HAGENT_LLM_MODEL="bedrock/us.meta.llama3-3-70b-instruct-v1:0"
```

For OpenAI gpt-oss 20B:
```
export HAGENT_LLM_MODEL="bedrock/us.openai.gpt-oss-20b-1:0"
```
