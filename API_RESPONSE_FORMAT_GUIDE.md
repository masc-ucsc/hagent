# API Response Format Guide

## Overview: Two Different OpenAI APIs

OpenAI has **two different API formats**:

1. **Chat Completions API** - Used by GPT-3.5, GPT-4, Llama, etc.
2. **Responses API** - Used by reasoning models (GPT-5-Codex, O1, O3-mini)

---

## 1. Chat Completions API (GPT-3.5, GPT-4, Llama)

### Request Format
```python
response = client.chat.completions.create(
    model="gpt-4",
    messages=[
        {"role": "system", "content": "You are a helpful assistant"},
        {"role": "user", "content": "Write a function that adds two numbers"}
    ],
    max_tokens=100
)
```

### Response Structure
```python
{
    "id": "chatcmpl-abc123",
    "object": "chat.completion",
    "created": 1234567890,
    "model": "gpt-4-0613",
    "choices": [
        {
            "index": 0,
            "message": {
                "role": "assistant",
                "content": "def add(a, b):\n    return a + b"
            },
            "finish_reason": "stop"
        }
    ],
    "usage": {
        "prompt_tokens": 20,
        "completion_tokens": 15,
        "total_tokens": 35
    }
}
```

### Text Extraction
```python
# Standard extraction
text = response.choices[0].message.content

# litellm handles this automatically
text = response['choices'][0]['message']['content']
```

---

## 2. Responses API (GPT-5-Codex, O1, O3-mini)

### Request Format
```python
response = client.responses.create(
    model="gpt-5-codex",
    input="Write a function that adds two numbers",  # Single string, NOT messages!
    max_output_tokens=100  # Note: max_output_tokens, not max_tokens
)
```

### Response Structure
```python
Response(
    id='resp_abc123',
    object='response',
    created_at=1762720143.0,
    status='incomplete',
    model='gpt-5-codex',

    output=[
        # Item 0: Reasoning (internal thought process)
        ResponseReasoningItem(
            type='reasoning',
            reasoning='<internal reasoning not exposed>'
        ),

        # Item 1: Message (actual output)
        ResponseOutputMessage(
            type='message',
            content=[
                OutputTextContentBlock(
                    type='output_text',
                    text='def add(a, b):\n    return a + b'
                )
            ]
        )
    ],

    # Convenience property - aggregates all output_text items
    output_text='def add(a, b):\n    return a + b',

    usage=ResponseUsage(
        input_tokens=14,
        output_tokens=50,
        total_tokens=64,
        output_tokens_details=OutputTokensDetails(reasoning_tokens=0)
    )
)
```

### Text Extraction

**Recommended (using output_text property)**:
```python
text = response.output_text
```

**Fallback (manual extraction)**:
```python
texts = []
for item in response.output:
    if item.type == 'message':
        for content_block in item.content:
            if content_block.type == 'output_text':
                texts.append(content_block.text)
text = '\n\n'.join(texts)
```

---

## Key Differences Summary

| Feature | Chat Completions API | Responses API |
|---------|---------------------|---------------|
| **Models** | GPT-3.5, GPT-4, Llama | GPT-5-Codex, O1, O3 |
| **Endpoint** | `client.chat.completions.create()` | `client.responses.create()` |
| **Input** | `messages=[{...}]` (list) | `input="..."` (string) |
| **Token Limit** | `max_tokens` | `max_output_tokens` |
| **Output** | `response.choices[]` | `response.output[]` |
| **Text Location** | `choices[0].message.content` | `output_text` property |
| **Reasoning** | No reasoning steps | May include reasoning items |
| **Usage Fields** | `prompt_tokens`, `completion_tokens` | `input_tokens`, `output_tokens` |
| **litellm Support** | ✅ Full support | ❌ Not supported yet |

---

## How HAgent Handles Both

### In `llm_wrap.py` (hagent/core/llm_wrap.py)

```python
# Detect reasoning models
responses_api_keywords = ['gpt-5-codex', 'gpt-5', 'o3-mini', 'o3', 'o1-mini', 'o1']
use_responses_api = any(keyword in model.lower() for keyword in responses_api_keywords)

if use_responses_api:
    # Call Responses API directly (litellm doesn't support it)
    return self._call_openai_responses_api(messages, model, n, llm_call_args)
else:
    # Use litellm for standard models
    response = litellm.completion(**llm_call_args)
    text = response['choices'][0]['message']['content']
```

### In `_call_openai_responses_api()`:

```python
# Try output_text property first
if hasattr(response, 'output_text'):
    response_text = response.output_text

    # Fallback: extract from output items if output_text is empty
    if not response_text and hasattr(response, 'output'):
        texts = []
        for item in response.output:
            if hasattr(item, 'text') and item.text:
                texts.append(item.text)
            elif hasattr(item, 'content') and isinstance(item.content, list):
                for content_item in item.content:
                    if hasattr(content_item, 'text'):
                        texts.append(content_item.text)
        response_text = '\n\n'.join(texts)
```

---

## Why the Empty Response Issue Occurred

1. **Output structure**: GPT-5-Codex returns `output[]` with:
   - `output[0]`: Reasoning item (type='reasoning')
   - `output[1]`: Message item (type='message' with content)

2. **output_text property**: Aggregates ONLY items with `type='output_text'`

3. **Edge case**: Sometimes the text is in `output[1].content[0].text` but NOT captured by `output_text`

4. **Our fix**: Added fallback to manually extract from `output[].text` and `output[].content[].text`

---

## Testing

Run the comparison test:
```bash
uv run python test_response_structure_comparison.py
```

This shows the exact structure differences between both APIs.
