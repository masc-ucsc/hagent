
curl -LsSf https://astral.sh/uv/install.sh | sh

cd /code/hagent &&
  UV_PROJECT_ENVIRONMENT=/tmp/venv uv sync &&
  /tmp/venv/bin/python scripts/hagent-build.py --help

  UV_PROJECT_ENVIRONMENT=/tmp/venv VIRTUAL_ENV=/tmp/venv uv run ./scripts/hagent-build.py

-------

- hagent.yaml uses a "script". ./scripts/gcd_compile ./scripts/gcd_lint ....

  + each command executes the associated command.
       It reads the BUILD_DIR for output directory or current directory if unset
       It reads the HAGENT_WORKDIR_REPO if set or current directory otherwise.

       (commands like the yosys need to use both to point to the correct direction)

  + Change the track_dir to track_repo_dir track_build_dir so that they read the directory output/input automatically.
    Assume that track_repo_dir is not generated, build_dir are generated when the associmated command is executed

  + Fix the hagent.yaml for simplechisel/XiangShan

- Create the MCP that reads the hagent.yaml and hagent-build.py so that it is exposed to claude code

-------
This document has a dump of "potential" TODOs, many are likely to be bad ideas.

# Use 3.14 template format?

```
# New t-string approach - deferred evaluation
template = t"Hello, {name}!"  # Creates a template, doesn't evaluate yet

# Now we can reuse this template with different contexts
context1 = {"name": "Bob"}
context2 = {"name": "Charlie"}

print(template.substitute(context1))  # Hello, Bob!
print(template.substitute(context2))  # Hello, Charlie!
```

# Docker



Avoid warning:

 docker run --platform linux/amd64 -it --rm mascucsc/hagent-builder:latest

Overlays:

sudo mkdir -p /mnt/merged
sudo chown user /mnt/merged
sudo mount -t overlay overlay -o lowerdir=/mnt/lower,upperdir=/mnt/overlay/upper,workdir=/mnt/overlay/work /mnt/merged

# Small TODOs

 check_equivalence should have a "top" argument (multiple modules)
   Fix v2chisel to pass as argument

 Fix all the llm_wrap calls/configs
 Create class to extract code from markdown from text and return in list

# Create easy install for non-hagent developers

 Something like this?

```
 npx https://github.com/masc-ucsc/hagent
```

# Docker related

 Mirror a bit the CVDP structure?
   /code/prompt.json  # entry prompt
   /code/rtl
   /code/verif
   /code/docs
   /code/rundir  # logs and results from agentic run
   /app          # installed tools custom run

# New Passes

## Guardrails

 Many prompts can have questions/answers that go off-topic. A simple guardrail for user prompt makes sense.

## CompileBugFix

 + Use a DB with one-shot sample fixes.
 + Insert markers in comments for location (or region if unclear).
 + Provide specification if existing too
 + Iterate over several LLMs and mixes/prompts for cost saving and speed.

## RungimeBugFix

 There are several degrees of feedback that can be passed to fix a bug. Providing all is not always the best https://arxiv.org/abs/2412.03905

 Feedback:
  -
