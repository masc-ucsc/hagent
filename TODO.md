-------

In equiv_check.py, we do not need to have use_docker. If container_manger is not None, we are in use_docker mode

-------

Container_manager.setup accepts a workdir as option, we should remove this as it is not needed.

-------
This code in path_manager.py seems wrong:
```
    def _validate_docker_mode(self) -> None:
        """Validate environment variables for Docker execution mode."""
        # In Docker mode, only HAGENT_EXECUTION_MODE is required from user
        # Container manager will set the rest automatically inside the container

        # If we're inside a container, these will be set by container_manager
        if os.environ.get('HAGENT_REPO_DIR'):
            self._repo_dir = Path(os.environ['HAGENT_REPO_DIR']).resolve()
        if os.environ.get('HAGENT_BUILD_DIR'):
            self._build_dir = Path(os.environ['HAGENT_BUILD_DIR']).resolve()
        if os.environ.get('HAGENT_CACHE_DIR'):
            self._cache_dir = Path(os.environ['HAGENT_CACHE_DIR']).resolve()
```

The reason is that inside docker, we can not use Path to validate a path.

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
