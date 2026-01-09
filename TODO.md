-------

litellm also supports OpenAI codex, but there is code to switch to OpenAI API.

Nice to keep a single consistent litellm API

Main file: hagent/core/llm_wrap.py

-------

Create a cli/mcp/prompt/? that given a repo, creates a hagent.yaml (there should be some scripts to check correctness)

Similar to /init in tools but for hagent.yaml

-------
Several places in hagent.yaml says (/code/workspace/....), we should use HAGENT_... as needed to do auto replace

-------

Add to hagent.yaml in cva6 how to synthesize a submodule

/code/hagent/scripts/synth.py --sta --tech-dir /code/workspace/tech --netlist  ../build/netlist_id_stage.v --top cva6  --top-synthesis id_stage    --ignore-unknown-modules --allow-use-before-declare    core/include/cv64a6_imafdc_sv39_wb_config_pkg.sv -f ./core/Flist.cva6


time /code/hagent/scripts/synth.py --sta --tech-dir /code/workspace/tech --netlist  ../build/netlist.v --top cva6   --ignore-unknown-modules --allow-use-before-declare    core/include/cv64a6_imafdc_sv39_wb_config_pkg.sv -f ./core/Flist.cva6

-------

ciel ls-remote --pdk-family sky130 | head -1
6971617b18b2f322d8f574af7e53f79ddd75dafe

ciel enable --pdk-family sky130 6971617b18b2f322d8f574af7e53f79ddd75dafe

ls ${HOME}/.ciel/ciel/sky130/versions/6971617b18b2f322d8f574af7e53f79ddd75dafe/sky130A/libs.ref/sky130_fd_sc_hd/lib/
sky130_fd_sc_hd__ff_100C_1v65.lib           sky130_fd_sc_hd__ff_n40C_1v95.lib  sky130_fd_sc_hd__ss_n40C_1v44.lib
sky130_fd_sc_hd__ff_100C_1v95.lib           sky130_fd_sc_hd__ss_100C_1v40.lib  sky130_fd_sc_hd__ss_n40C_1v60_ccsnoise.lib
sky130_fd_sc_hd__ff_n40C_1v56.lib           sky130_fd_sc_hd__ss_100C_1v60.lib  sky130_fd_sc_hd__ss_n40C_1v60.lib
sky130_fd_sc_hd__ff_n40C_1v65.lib           sky130_fd_sc_hd__ss_n40C_1v28.lib  sky130_fd_sc_hd__ss_n40C_1v76.lib
sky130_fd_sc_hd__ff_n40C_1v76.lib           sky130_fd_sc_hd__ss_n40C_1v35.lib  sky130_fd_sc_hd__tt_025C_1v80.lib
sky130_fd_sc_hd__ff_n40C_1v95_ccsnoise.lib  sky130_fd_sc_hd__ss_n40C_1v40.lib  sky130_fd_sc_hd__tt_100C_1v80.lib

-------

When I run pytest with --durations option, I see that these are slow tests:

23.77s call     hagent/step/replicate_code/tests/test_replicate_code.py::test_replicate_code
8.56s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_multiple_checks
5.42s call     hagent/tool/tests/test_cli_equiv_check.py::test_cli_equivalent_designs
5.29s call     hagent/tool/tests/test_cli_equiv_check.py::test_cli_non_equivalent_designs
4.84s call     hagent/step/trivial/tests/test_cli_trivial.py::TestTrivialCLI::test_docker_execution_no_env_vars
4.55s call     hagent/step/trivial/tests/test_cli_trivial.py::TestTrivialCLI::test_docker_execution_with_repo_mount
4.49s call     hagent/tool/tests/test_cli_equiv_check.py::test_cli_specific_top_module
4.23s call     hagent/step/trivial/tests/test_cli_trivial.py::TestTrivialCLI::test_docker_execution_with_absolute_paths
4.13s call     hagent/inou/tests/test_executor_yosys_synthesis.py::TestExecutorYosysSynthesis::test_simple_verilog_synthesis
3.96s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_file_management
3.84s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_syntax_error_handling
3.76s call     hagent/tool/tests/test_equiv_check_docker.py::test_docker_integration_standalone
3.75s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_non_equivalent_designs
3.71s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_equivalent_designs
3.58s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_and_gate_equivalence

70.00s call    hagent/step/replicate_code/tests/test_replicate_code.py::test_replicate_code
21.77s call    hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_multiple_checks
8.27s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_file_management
8.26s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_and_gate_equivalence
8.12s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_equivalent_designs
8.05s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_syntax_error_handling
8.03s call     hagent/tool/tests/test_equiv_check_docker.py::TestEquivCheckDocker::test_docker_non_equivalent_designs
7.87s call     hagent/tool/tests/test_equiv_check_docker.py::test_docker_integration_standalone
4.45s call     hagent/inou/tests/test_executor_yosys_synthesis.py::TestExecutorYosysSynthesis::test_simple_verilog_synthesis
4.35s call     hagent/inou/tests/test_executor_yosys_synthesis.py::TestExecutorYosysSynthesis::test_multiple_file_synthesis
4.06s call     hagent/step/trivial/tests/test_cli_trivial.py::TestTrivialCLI::test_docker_execution_with_absolute_paths
4.03s call     hagent/step/trivial/tests/test_cli_trivial.py::TestTrivialCLI::test_docker_execution_no_env_vars
3.86s call     hagent/step/trivial/tests/test_cli_trivial.py::TestTrivialCLI::test_docker_execution_with_repo_mount
3.10s call     hagent/inou/tests/test_executor_yosys_synthesis.py::TestExecutorYosysSynthesis::test_yosys_script_execution

Can we provide test_replicate_code and test_equiv_checker_docker to see which function is using most of the time? We should try to speedup that task.

-----

mada4:

 docker run -it -v ./tmp/repo:/code/workspace/repo -v /mada/software/techfiles/sky130_fd_sc/:/code/workspace/tech --rm mascucsc/hagent-simplechisel:2026.01

 fix hagent.yaml so that it can run synth.rb

xiangshan:

 ../../hagent/scripts/synth.py --exclude SimTop.sv --liberty ../tech/sky130_fd_sc_hd__ff_100C_1v95.lib --ignore-unknown-modules -DSYNTHESIS --top XSCore -I ./build_opt/generated-src/ -F ./build_opt/rtl/filelist.f

pipeline:

 ../../hagent/scripts/synth.py --liberty ../tech/sky130_fd_sc_hd__ff_100C_1v95.lib --top PipelinedDualIssueCPU -F ./build_pipelined_d/filelist.f  --sta

-------

 Issue with compile singlecycle cpu (does not show in build directory in tmp/potato/build/*)

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

If HAGENT_LLM_MODEL is set, it uses this LLM for all the queries.

Usuful when users do not have  the keys used for regression testing.

-------
Input/output schema and parameters field in the fastmcp

The compile errors/messages could be structured as an output schema.

What are the parameters?

-------

The compile/lint should return a bit more structured output

Maybe filter just the error messages, otherwise list files so that gemini can handle it faster, not to start to look for the file.

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
  HAGENT_DOCKER: "docker"  # define to enable docker mode
  mount_build_dir: ./xxx
  mount_cache_dir: ./xxx
  mount_repo_dir: ./xxx

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

-------
## Chipyard

Chipyard deprecated their docker, so we need to create a new one. It is quite similar to the original, but the "chipyard" repository is NOT inside the docker. Just the build tools. This allows to track the edited files.

1-Get Chipyard repo:
```bash
git clone https://github.com/ucb-bar/chipyard.git
cd chipyard
# Get a stable chipyard version (last tested 1.13.0)
git checkout 1.13.0
```


2-Use the HAgent docker (allows chipyard and yosys)


```bash
# May require sudo dependent on your setup/permissions
docker pull ucbbar/chipyard-image
```
