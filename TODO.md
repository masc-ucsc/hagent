-------

No python code (except tests) should set HAGENT_... as those are environment variables.

Remove and fix accordingly

-------

 Issue with compile singlecycle cpu (does not show in build directory in tmp/potato/build/*)

-------

 Add a check to look for too long functions. Then rank them error based on function lenght. If more than 1-2 scrren (60LoC), issue waring to refactor.

-------

The docker run output has /code/workspace/... directories, but the message passed back should "search-replace" the docker for the HAGENT_... variable set. Otherwise, the MCP can not know the path to fix.

 │ x  hagent.build (hagent MCP Server) {"name":"gcd","api":"compile"}                                                   │
 │                                                                                                                      │
 │    MCP error -32603: ❌ COMPILATION FAILED (exit code: 1)                                                            │
 │                                                                                                                      │
 │    🔧 SUGGESTION: There appears to be a Scala compilation error. Please check and fix the Scala source files.        │
 │                                                                                                                      │
 │    📁 FILES TO CHECK: /code/workspace/repo/src/main/scala/gcd/GCD.scala:34                                           │
 │                                                                                                                      │
 │    ❌ ERROR: [error] /code/workspace/repo/src/main/scala/gcd/GCD.scala:34:3: not found: value io_outputGCD...        │
 │                                                                                                                      │
 │    🔍 SPECIFIC ERROR: [error] /code/workspace/repo/src/main/scala/gcd/GCD.scala:34:3: not found: value               │
 │    io_outputGCD...

-------

hagent/inou has several objects, but Python classes outside hagent should only use Runner or Builder.


Builder is mostly a wrapper around Runner for the case that we have a hagent.yaml configuration.


container_manager, FileTracker and PathManager should not be used like equiv_check.py does, but use Runner or Builder (running in the case of equiv_check)


-------

container_manager has issues with HAGENT_*_DIR setup. It should never be set to /code/workspace/...

The code sets it, and then in several places does not thing if set there. Overall, it should not set the environment variables in container_manager to /cpde/workspace.

If inside docker running hagent, the container_manager should not be called after all.

Not sure that we need the "automount" option in container_manager.setup

-------

If HAGENT_LLM_MODEL is set, it uses this LLM for all the queries.

Usuful when users do not have  the keys used for regression testing.

-------
Input/output schema and parameters field in the fastmcp 

The compile errors/messages could be structured as an output schema.

What are the parameters?

-------

The current @hagent/mcp/hagent-mcp-server.py is a fastmcp server that registers multiple mcp tools like @hagent/mcp/mcp_build.py

The current mcp_build.py schema is not respected and hagent-mcp-server rewrites it in a different way. For example, it provides a 
very short title instead of a longer description.

When I run:
```
export UV_PROJECT="/Users/renau/projs/hagent"
export HAGENT_ROOT="/Users/renau/projs/hagent"
export HAGENT_DOCKER="mascucsc/hagent-simplechisel:2025.09r"
export HAGENT_REPO_DIR="/Users/renau/tmp/potato/repo"
export HAGENT_BUILD_DIR="/Users/renau/tmp/potato/build"
export HAGENT_CACHE_DIR="/Users/renau/tmp/potato/cache"
export HAGENT_OUTPUT_DIR=/Users/renau/tmp/potato/log
export HAGENT_EXECUTION_MODE="docker"

(echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}'; echo '{"jsonrpc":"2.0","method":"notifications/initialized"}'; echo '{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}') | uv run python ./hagent/mcp/hagent-mcp-server.py | jq '.result.tools[] | select(.name == "hagent.build")'
```

----

The compile/lint should return a bit more structured output

Maybe filter just the error messages, otherwise list files so that gemini can handle it faster, not to start to look for the file.

-------

Both gemini and claude code can use the mcp add name script, so we should remove the 

hagent_mcp_conf.json

and associated code for it

-------

In equiv_check.py, we do not need to have use_docker. If container_manger is not None, we are in use_docker mode

-------

Run local after removing local and see if it fails, if not no need to patch this

Several tests need a working repo/cache/build directory. When needed to run one for test reasons, let's be consistent and make sure that all use the output/local/repo output/local/build and output/local/cache instead of ./local

-------

In step objects, we use self.error to set an error. In many other code places, we use self.set_error. For consistency, we should rename the code in hagent/core/step.py to use set_error (and associated files in hagent/step/**.py)

-------

To copy files inside the docker, several times (equiv_check.py), we use a "cat" command passed to the container_manager.run

It may be nicer if we create a write_file method in container_manager.

-------

Add option to mount repo/cache/build dir from local instead of mounting.

-------
container_manager:create_container is not testing in test_container_manager.

 Maybe the test for this should do this:
  Create a temp directory
   -git clone https://github.com/masc-ucsc/simplechisel repo
   -Create a cache and build
   -mount hagent directory '/code/hagent'
   -Make sure that the venv works runing something simple like `uv run python ./scripts/hagent-build.py --config $HAGENT_REPO_DIR/hagent.yaml --list`

-------

When I run:
```
 HAGENT_CACHE_DIR=./local/cache HAGENT_BUILD_DIR=./local/build/ HAGENT_REPO_DIR=./local/repo/ HAGENT_EXECUTION_MODE=docker uv run python ./hagent/tool/tests/test_equiv_check_docker.py
```

It creates files in the repo directory:
```
local/repo/check.s                      local/repo/gold.v                       local/repo/smt_method_0_stdout.log
local/repo/gate.v                       local/repo/smt_method_0_stderr.log
```
and the cache/inou:
```
local/cache/inou/equiv_check_jd7sikuu
```

It should only create the cache/inou, it should not create files in the repo for this type of test. equiv_check, should only create a temporary directory in cache/inou/equiv_check_??????

-------

Maybe create a shared "hagent" setup section that it is shared across all the passes when set in the input yaml.

hagent:
  execution_mode: "docker" # (or local)
  mount_build_dir: ./xxx
  mount_cache_dir: ./xxx
  mount_repo_dir: ./xxx


-------
curl -LsSf https://astral.sh/uv/install.sh | sh

cd /code/hagent &&
  UV_PROJECT_ENVIRONMENT=/code/workspace/cache/venv uv sync &&
  /tmp/venv/bin/python scripts/hagent-build.py --help

  UV_PROJECT_ENVIRONMENT=/code/workspace/cache/venv VIRTUAL_ENV=/code/workspace/cache/venv uv run /code/hagent/scripts/hagent-build.py --config $HAGENT_REPO_DIR/hagent.yaml



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
