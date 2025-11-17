<a id="core.llm_wrap"></a>

# core.llm\_wrap

<a id="core.llm_template"></a>

# core.llm\_template

<a id="core.tests.test_llm_wrap"></a>

# core.tests.test\_llm\_wrap

<a id="core.tests.test_llm_template"></a>

# core.tests.test\_llm\_template

<a id="core.step"></a>

# core.step

<a id="step.generate_code.generate_code"></a>

# step.generate\_code.generate\_code

<a id="step.generate_code.tests.test_generate_code"></a>

# step.generate\_code.tests.test\_generate\_code

<a id="step.generate_code.tests.test_generate_code.clean_generated_dir"></a>

#### clean\_generated\_dir

```python
@pytest.fixture
def clean_generated_dir(tmp_path)
```

Fixture to provide a temporary directory and ensure cleanup after tests.

<a id="step.generate_code.tests.test_generate_code.test_generate_missing_llm"></a>

#### test\_generate\_missing\_llm

```python
def test_generate_missing_llm(tmp_path)
```

Test that setup fails when 'llm' is missing in input YAML.

<a id="step.generate_code.tests.test_generate_code.test_generate_code"></a>

#### test\_generate\_code

```python
def test_generate_code(tmp_path)
```

Test generating code with a full input YAML.

<a id="step.generate_code.tests.test_generate_code.test_generate_custom_module_name"></a>

#### test\_generate\_custom\_module\_name

```python
def test_generate_custom_module_name(tmp_path)
```

Test generating code with a custom module name.

<a id="step.generate_code.tests.test_generate_code.test_generate_empty_description"></a>

#### test\_generate\_empty\_description

```python
def test_generate_empty_description(tmp_path)
```

Test generating code with an empty description.

<a id="step.generate_code.tests.test_generate_code.test_generate_empty_llm_response"></a>

#### test\_generate\_empty\_llm\_response

```python
def test_generate_empty_llm_response(tmp_path)
```

Test generating code when LLM returns an empty response.

<a id="step.v2chisel_pass1.v2chisel_pass1"></a>

# step.v2chisel\_pass1.v2chisel\_pass1

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1"></a>

# step.v2chisel\_pass1.tests.test\_v2chisel\_pass1

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.valid_input_file"></a>

#### valid\_input\_file

```python
@pytest.fixture
def valid_input_file(tmp_path)
```

Create a valid input YAML file with 'llm' and minimal verilog/chisel data.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.step_with_io"></a>

#### step\_with\_io

```python
@pytest.fixture
def step_with_io(valid_input_file, tmp_path)
```

Return a V2ChiselPass1 Step object with a valid input path and a temp output path.
NOTE: We won't call .setup() here; each test can do so at the desired time.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_no_valid_snippet_generated"></a>

#### test\_no\_valid\_snippet\_generated

```python
def test_no_valid_snippet_generated(step_with_io)
```

- LLM never produces valid code after all attempts (empty or invalid).
- We expect 'No valid snippet generated.' in chisel_updated and was_valid=False.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_chisel2v_empty_snippet"></a>

#### test\_chisel2v\_empty\_snippet

```python
def test_chisel2v_empty_snippet(step_with_io)
```

- LLM returns a snippet that is empty after _strip_markdown_fences.
- _run_chisel2v should detect empty snippet and fail immediately.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_chisel2v_no_module_keyword"></a>

#### test\_chisel2v\_no\_module\_keyword

```python
def test_chisel2v_no_module_keyword(step_with_io)
```

Force all attempts to produce Verilog with *no* 'module' substring => remain invalid.
Expect final was_valid=False and "No valid snippet generated.".

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_chisel2v_exception"></a>

#### test\_chisel2v\_exception

```python
def test_chisel2v_exception(step_with_io)
```

Chisel2v.generate_verilog throws an exception every time => all 5 attempts fail.
Final snippet => 'No valid snippet generated.'.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_chisel_classname_extraction"></a>

#### test\_chisel\_classname\_extraction

```python
def test_chisel_classname_extraction(step_with_io)
```

- `_find_chisel_classname` finds the class name if present.
- If not found, fallback to 'MyModule'.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_missing_llm_section"></a>

#### test\_missing\_llm\_section

```python
def test_missing_llm_section(tmp_path)
```

Test that an error is raised when 'llm' section is missing in input YAML.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_missing_prompt1_file"></a>

#### test\_missing\_prompt1\_file

```python
def test_missing_prompt1_file(step_with_io, tmp_path)
```

Test that an error is raised when 'prompt1.yaml' file is missing.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_llm_returns_empty_response"></a>

#### test\_llm\_returns\_empty\_response

```python
def test_llm_returns_empty_response(step_with_io)
```

Test handling when LLM returns an empty response.

<a id="step.v2chisel_pass1.tests.test_v2chisel_pass1.test_chisel2v_setup_failure"></a>

#### test\_chisel2v\_setup\_failure

```python
def test_chisel2v_setup_failure(step_with_io)
```

Test that an error is returned when Chisel2v.setup() fails.

<a id="step.use_chisel2v"></a>

# step.use\_chisel2v

<a id="step.use_chisel2v.extract_module_name"></a>

#### extract\_module\_name

```python
def extract_module_name(chisel_code: str) -> str
```

Extracts the module (class) name from the Chisel code.
Assumes the module is defined as: class ModuleName extends Module

<a id="step.trivial.trivial"></a>

# step.trivial.trivial

<a id="step.trivial.tests.test_trivial"></a>

# step.trivial.tests.test\_trivial

<a id="step.replicate_code.tests.test_replicate_code"></a>

# step.replicate\_code.tests.test\_replicate\_code

<a id="step.replicate_code.replicate_code"></a>

# step.replicate\_code.replicate\_code

<a id="step.v2chisel_fix.v2chisel_fix"></a>

# step.v2chisel\_fix.v2chisel\_fix

__V2ChiselFix__


**V2ChiselFix** is a step in the hardware design automation pipeline designed to refine Chisel code based on Logic Equivalence Check (LEC) results. It leverages a Language Model (LLM) to iteratively improve Chisel code when discrepancies are found between generated Verilog and fixed Verilog specifications.

## Usage

Run the pass using Poetry:

```bash
poetry run python3 hagent/step/v2chisel_fix/v2chisel_fix.py -o hagent/step/v2chisel_fix/out2.yaml hagent/step/v2chisel_pass1/out2.yaml

<a id="step.v2chisel_fix.v2chisel_fix.V2ChiselFix"></a>

## V2ChiselFix Objects

```python
class V2ChiselFix(Step)
```

<a id="step.v2chisel_fix.v2chisel_fix.V2ChiselFix.run"></a>

#### run

```python
def run(data)
```

1) Reads 'chisel_pass1' data.
2) Calls LEC to see if verilog_candidate == verilog_fixed.
3) If LEC fails, iteratively refine via LLM up to lec_limit times.
4) Return final data with "chisel_fixed" in the YAML.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix"></a>

# step.v2chisel\_fix.tests.test\_v2chisel\_fix

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.valid_input_file"></a>

#### valid\_input\_file

```python
@pytest.fixture
def valid_input_file(tmp_path)
```

Creates a minimal valid YAML for V2ChiselFix:
  - 'chisel_pass1' with some snippet
  - 'verilog_fixed'
  - 'llm' if needed

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.step_with_io"></a>

#### step\_with\_io

```python
@pytest.fixture
def step_with_io(valid_input_file, tmp_path)
```

Returns a V2ChiselFix step with an input path and a temp output.
We'll call .setup() and then use run(input_data) to get the result.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_missing_chisel_pass1"></a>

#### test\_missing\_chisel\_pass1

```python
def test_missing_chisel_pass1(tmp_path)
```

If 'chisel_pass1' isn't in the YAML => raises ValueError

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_no_prompt3_file"></a>

#### test\_no\_prompt3\_file

```python
def test_no_prompt3_file(step_with_io)
```

If prompt3.yaml doesn't exist => prints a warning, refine_llm=None.
Run normally so no refinement occurs.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_prompt3_but_no_llm_config"></a>

#### test\_prompt3\_but\_no\_llm\_config

```python
def test_prompt3_but_no_llm_config(tmp_path)
```

If prompt3.yaml exists but there's no 'llm' config => warn and refine_llm=None.
Run normally so no refinement occurs.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_already_equiv_no_refine"></a>

#### test\_already\_equiv\_no\_refine

```python
def test_already_equiv_no_refine(step_with_io)
```

LEC passes initially so no refinement is done.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_lec_fails_refine_succeeds"></a>

#### test\_lec\_fails\_refine\_succeeds

```python
def test_lec_fails_refine_succeeds(step_with_io, tmp_path)
```

LEC fails initially, then a refinement produces a new snippet and verilog,
so that equivalence passes on the second check.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_lec_fails_all_attempts"></a>

#### test\_lec\_fails\_all\_attempts

```python
def test_lec_fails_all_attempts(step_with_io, tmp_path)
```

LEC fails for all attempts; after reaching lec_limit the result has equiv_passed=False.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_lec_fails_refine_cannot_improve"></a>

#### test\_lec\_fails\_refine\_cannot\_improve

```python
def test_lec_fails_refine_cannot_improve(step_with_io, tmp_path)
```

LEC fails and the LLM returns the same code (no improvement) so refinement stops.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_refine_llm_not_present"></a>

#### test\_refine\_llm\_not\_present

```python
def test_refine_llm_not_present(step_with_io)
```

If there's no prompt3.yaml then refine_llm is None so _refine_chisel_code returns the original code.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_refine_chisel_code_empty_response"></a>

#### test\_refine\_chisel\_code\_empty\_response

```python
def test_refine_chisel_code_empty_response(step_with_io)
```

If LLM returns an empty response, the original code is kept.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_refine_chisel_code_no_fences"></a>

#### test\_refine\_chisel\_code\_no\_fences

```python
def test_refine_chisel_code_no_fences(step_with_io)
```

When LLM returns triple backticks, they are stripped.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_generate_verilog_missing_module"></a>

#### test\_generate\_verilog\_missing\_module

```python
def test_generate_verilog_missing_module(step_with_io)
```

Test _generate_verilog returns an error when generated Verilog lacks the 'module' keyword.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_generate_verilog_exception"></a>

#### test\_generate\_verilog\_exception

```python
def test_generate_verilog_exception(step_with_io)
```

Test _generate_verilog catches an exception from c2v.generate_verilog.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_check_equivalence_ok"></a>

#### test\_check\_equivalence\_ok

```python
def test_check_equivalence_ok(step_with_io)
```

Test _check_equivalence when equivalence returns True.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_check_equivalence_false"></a>

#### test\_check\_equivalence\_false

```python
def test_check_equivalence_false(step_with_io)
```

Test _check_equivalence when equivalence returns False and a counterexample is provided.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_check_equivalence_none_result"></a>

#### test\_check\_equivalence\_none\_result

```python
def test_check_equivalence_none_result(step_with_io)
```

Test _check_equivalence when the equivalence check returns None.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_check_equivalence_exception"></a>

#### test\_check\_equivalence\_exception

```python
def test_check_equivalence_exception(step_with_io)
```

Test _check_equivalence when an exception is thrown.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_check_equivalence_missing_code"></a>

#### test\_check\_equivalence\_missing\_code

```python
def test_check_equivalence_missing_code(step_with_io)
```

Test _check_equivalence when gold or reference code is missing.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_strip_markdown_fences"></a>

#### test\_strip\_markdown\_fences

```python
def test_strip_markdown_fences(step_with_io)
```

Test that markdown fences (with optional language tags) are removed.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_setup_no_prompt3_warning"></a>

#### test\_setup\_no\_prompt3\_warning

```python
def test_setup_no_prompt3_warning(tmp_path)
```

Test that a warning is printed when 'prompt3.yaml' is not found,
and that refine_llm remains None.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_run_missing_verilog_fixed"></a>

#### test\_run\_missing\_verilog\_fixed

```python
def test_run_missing_verilog_fixed(step_with_io, tmp_path)
```

Test that if 'verilog_fixed' is missing the LEC check is skipped.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_run_equiv_check_setup_failure"></a>

#### test\_run\_equiv\_check\_setup\_failure

```python
def test_run_equiv_check_setup_failure(step_with_io)
```

Test that if Equiv_check.setup() fails, an error is printed and equivalence check fails.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_refine_chisel_code_empty_after_strip"></a>

#### test\_refine\_chisel\_code\_empty\_after\_strip

```python
def test_refine_chisel_code_empty_after_strip(step_with_io)
```

Test that if LLM returns code that is empty after stripping markdown fences,
the original code is kept.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_generate_verilog_setup_failure"></a>

#### test\_generate\_verilog\_setup\_failure

```python
def test_generate_verilog_setup_failure(step_with_io)
```

Test that _generate_verilog returns (None, error_message) when Chisel2v.setup() fails.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_generate_verilog_missing_module_keyword"></a>

#### test\_generate\_verilog\_missing\_module\_keyword

```python
def test_generate_verilog_missing_module_keyword(step_with_io)
```

Test that _generate_verilog returns an error when generated Verilog lacks 'module' keyword.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_refinement_with_verilog_generation_failure"></a>

#### test\_refinement\_with\_verilog\_generation\_failure

```python
def test_refinement_with_verilog_generation_failure(step_with_io, tmp_path)
```

Test the case where Verilog generation fails during refinement.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_successful_verilog_generation_no_error"></a>

#### test\_successful\_verilog\_generation\_no\_error

```python
def test_successful_verilog_generation_no_error(step_with_io)
```

Test that _generate_verilog returns (verilog_output, None) on a successful run.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_setup_prompt3_exists_but_empty_llm_config"></a>

#### test\_setup\_prompt3\_exists\_but\_empty\_llm\_config

```python
def test_setup_prompt3_exists_but_empty_llm_config(tmp_path)
```

If prompt3.yaml exists and the 'llm' config is empty, warn and set refine_llm to None.

<a id="step.v2chisel_fix.tests.test_v2chisel_fix.test_generate_verilog_success"></a>

#### test\_generate\_verilog\_success

```python
def test_generate_verilog_success(step_with_io)
```

Test that _generate_verilog returns (verilog_output, None) on a successful run.

<a id="tool.compile_slang"></a>

# tool.compile\_slang

<a id="tool.compile_slang.Compile_slang"></a>

## Compile\_slang Objects

```python
class Compile_slang()
```

A HAgent tool pyslang (slang) wrapper to compile and extract information from Verilog.

<a id="tool.compile_slang.Compile_slang.__init__"></a>

#### \_\_init\_\_

```python
def __init__()
```

Initializes the SlangTool instance with a new pyslang.Compilation object,
an empty error message

<a id="tool.compile_slang.Compile_slang.setup"></a>

#### setup

```python
def setup() -> bool
```

Validates the presence of the pyslang package.
Does not raise exceptions; returns True if setup is successful, False otherwise.
Updates error_message on failure.
Initializes self._compiler with these options:
copt = pyslang.CompilationOptions()
copt.errorLimit = 1
copt.flags = pyslang.CompilationFlags.IgnoreUnknownModules

**Returns**:

- `bool` - True if setup is successful, False otherwise.

<a id="tool.compile_slang.Compile_slang.add_source"></a>

#### add\_source

```python
def add_source(text: Optional[str] = None, file: Optional[str] = None) -> bool
```

Either text or file must be provided.
Depending on the input type, uses pyslang.SyntaxTree.fromText or pyslang.SyntaxTree.fromFile.

**Arguments**:

- `text` _str_ - The input string
- `file` _str_ - The input file to use

**Returns**:

  The source included may have compile errors, the error_message is
  only updated if the file did not exist or an exception is raised by
  slang.

<a id="tool.compile_slang.Compile_slang.set_top"></a>

#### set\_top

```python
def set_top(top: str) -> bool
```

Using the currently compiled files, set the top. If it does not exist, it returns false, but no error_message is set.

**Returns**:

  True if the top exist in the compile (previously add_source) source. False otherwise.

<a id="tool.compile_slang.Compile_slang.get_hierarchy"></a>

#### get\_hierarchy

```python
def get_hierarchy(modname: str = "") -> List[str]
```

Extracts and returns a list of hierarchical names or identifiers by traversing
the top-level instances in the compilation root.

**Returns**:

- `List[str]` - A list of module or instance names representing the hierarchy.

<a id="tool.compile_slang.Compile_slang.get_ios"></a>

#### get\_ios

```python
def get_ios(modname: str = None) -> List[IO]
```

Extracts input/output definitions from the specified modname. If no module name is provided, the "top" is used.
It looks up the module by name and iterates through its body to extract port information (e.g., direction,
fixed range, name).

**Arguments**:

- `modname` _str_ - The name of the module to extract IO information from.

**Returns**:

- `List[IO]` - A list of IOs, Each entry has a named struct "name:str, input:bool, output:bool, bits:int".

<a id="tool.compile_slang.Compile_slang.get_warnings"></a>

#### get\_warnings

```python
def get_warnings() -> List[Diagnostic]
```

Retrieves and returns a list of formatted warning messages from the compilation diagnostics.
The returned List is a named struct with these fields:
msg: txt -- a single line complies with the gcc/clang error/warning format. E.g:
source:5:12: warning: implicit conversion truncates from 3 to 2 bits [-Wwidth-trunc]
loc: int -- the line of code (5) in the previous example
hint: txt -- The optional hint or more detailed multiline message. E.g:
assign c = a ^ tmp;
~ ^~~~~~~

**Returns**:

- `List[Diagnostic]` - A list of warning messages.

<a id="tool.compile_slang.Compile_slang.get_errors"></a>

#### get\_errors

```python
def get_errors() -> List[Diagnostic]
```

Retrieves and returns a list of formatted error messages from the compilation diagnostics.
The format is the same as the get_warnings

**Returns**:

- `List[Diagnostic]` - A list of error messages.

<a id="tool.trivial"></a>

# tool.trivial

<a id="tool.trivial.Trivial"></a>

## Trivial Objects

```python
class Trivial()
```

Trivial example of a tool.

<a id="tool.trivial.Trivial.__init__"></a>

#### \_\_init\_\_

```python
def __init__()
```

Initializes the Trivial object

<a id="tool.trivial.Trivial.setup"></a>

#### setup

```python
def setup(some_path: Optional[str] = None) -> bool
```

Checks that the tool is installed and ready to use. If not available.
Returns false, and sets an error_message. Does not raise an exception.

Returns True if Trivial is ready to use, False otherwise.

<a id="tool.react"></a>

# tool.react

<a id="tool.react.insert_comment"></a>

#### insert\_comment

```python
def insert_comment(code: str, add: str, prefix: str, loc: int) -> str
```

Inserts a multi-line comment into a string of code at a specific line number.

**Arguments**:

- `code` - The original string of code.
- `add` - The string containing the comment to be added.
- `prefix` - The comment prefix (e.g., "#" for Python, "//" for C/C++).
- `loc` - The line number (1-based index) where the comment should be inserted.
  

**Returns**:

  The modified string of code with the comment inserted.

<a id="tool.react.React"></a>

## React Objects

```python
class React()
```

Handles Re-Act iteration logic for external tools (e.g., compilers).
Does not invoke LLM logic directly; it orchestrates iteration steps and
calls user-supplied callbacks.
Exposes standard hagent tool interface methods (`setup`, plus custom
methods).
Example of external tool usage is a gcc compiler to fix/react with C++
code, or a ruff python tool, or a yosys for Verilog compilation.

<a id="tool.react.React.__init__"></a>

#### \_\_init\_\_

```python
def __init__()
```

Initialize internal states to defaults.

<a id="tool.react.React.setup"></a>

#### setup

```python
def setup(db_path: Optional[str] = None,
          learn: bool = False,
          max_iterations: int = 5,
          comment_prefix: str = '//') -> bool
```

Prepares the React tool for usage.
- Checks availability of DB (creates if missing and learn=True).
- Clears the last_code
- Loads or initializes the DB data.
- Sets _is_ready if successful.
- comment_prefix is the used language comment prefix

**Returns**:

  True if setup successful, False otherwise (and sets error_message).

<a id="tool.react.React.react_cycle"></a>

#### react\_cycle

```python
def react_cycle(initial_text: str, check_callback: Callable[[str], str],
                fix_callback: Callable[[str, str, str, int], str]) -> str
```

Orchestrates the Re-Act loop:
1. Send `initial_text` to `check_callback`.
2. If no error, return success immediately (returns initial_text).
3. If error, look up the error type in DB to retrieve sample fix text (if any).
   - The error follows the typical gcc/clang syntax
   "<filename>:<line number>:<column number>: <error/warning>: <message>"
   - Ignore the filename, but use the rest to select the BEGIN/END error insertion
4. Modifies the current_text with the BEGIN/END ERROR for error location (for demonstration, a simple appended note).
5. Pass the original text + error info + sample fix into `fix_callback`.
6. Check if progress is made, or if iteration limit is reached.
7. Possibly store new errors in DB if `learn=True`.
8. Return the text that has no errors or an empty string if it was not possible to fix.

<a id="tool.react.React.get_log"></a>

#### get\_log

```python
def get_log() -> List[Dict]
```

Returns the log of the iterations. Each entry in the list contains
the check and fix callback answers for that iteration.

<a id="tool.filter_lines"></a>

# tool.filter\_lines

<a id="tool.filter_lines.FilterLines"></a>

## FilterLines Objects

```python
class FilterLines()
```

A tool to filter Chisel code lines based on a generated Verilog diff.

It extracts tokens (including multi-digit numbers) from the diff’s code portion,
normalizes them (by splitting on underscores and camel-case boundaries), and then scores
each Chisel line (using only its code portion, ignoring inline comments) based on simple substring matching.

The union of candidate lines (excluding pure comment and import lines) is returned as a string
with each matching line prefixed with "HERE:?". An optional context parameter works similar
to grep’s -C flag.

This module supports both diff formats:
  - The “old” style with lines beginning with "<" or ">".
  - Unified diff format (as generated by difflib) with headers (---, +++, @@) and lines starting with "-" or "+".

<a id="tool.filter_lines.FilterLines.filter_lines"></a>

#### filter\_lines

```python
def filter_lines(diff_file: str, chisel_file: str, context: int = 0) -> str
```

Reads the diff file and the Chisel source file.

For each diff line that begins with a valid marker (after stripping leading whitespace)
("<", ">", "-", or "+"), the marker is stripped and the remaining text (ignoring inline comments)
is used to extract tokens. Any diff header lines (starting with '---', '+++', or '@@') are skipped.

Each Chisel line (using only its code portion, before any inline comment) is scored based on the
occurrence of these tokens. Additionally, if the diff line contains hint line numbers in its comment,
those candidate Chisel lines receive a score boost.

Pure comment lines and import statements in the Chisel file are skipped.

The union of candidate lines (i.e. lines with a positive score) is returned.
If 'context' is set to a value > 0, the specified number of lines before and after each candidate
line are also included. Candidate lines are prefixed with "HERE:?", while context lines are prefixed
with four spaces.

<a id="tool.fuzzy_grep"></a>

# tool.fuzzy\_grep

<a id="tool.fuzzy_grep.Fuzzy_grep"></a>

## Fuzzy\_grep Objects

```python
class Fuzzy_grep()
```

Fuzzy_grep tool class.

This tool can search a text, a list of files, or all files in a directory for fuzzy matches
based on provided search terms. The tool can be configured (via setup) with a language
so that reserved keywords for that language are ignored during matching.

<a id="tool.fuzzy_grep.Fuzzy_grep.__init__"></a>

#### \_\_init\_\_

```python
def __init__()
```

Initializes the Fuzzy_grep object.

<a id="tool.fuzzy_grep.Fuzzy_grep.setup"></a>

#### setup

```python
def setup(language: str = None) -> bool
```

Sets up the tool. If a language is specified, reserved keywords for that language
are used to filter out fuzzy matches.

Supported languages: 'verilog', 'scala', 'chisel'. If language is None, no filtering is done.
Returns True if setup is successful, False otherwise.

<a id="tool.fuzzy_grep.Fuzzy_grep.preprocess"></a>

#### preprocess

```python
@staticmethod
def preprocess(text: str) -> str
```

Remove underscores and digits from the input text and convert to lower-case.

<a id="tool.fuzzy_grep.Fuzzy_grep.extract_words"></a>

#### extract\_words

```python
@staticmethod
def extract_words(text: str) -> list
```

Split text into words based on word characters.

<a id="tool.fuzzy_grep.Fuzzy_grep.get_reserved_keywords"></a>

#### get\_reserved\_keywords

```python
@classmethod
def get_reserved_keywords(cls, language: str) -> set
```

Return a set of preprocessed reserved keywords for the given language.
Supported languages: 'verilog', 'scala', 'chisel'.
Returns an empty set if language is not recognized.

<a id="tool.fuzzy_grep.Fuzzy_grep.line_matches"></a>

#### line\_matches

```python
def line_matches(line: str, search_terms: list, threshold: int) -> bool
```

Returns True if for every search term, at least one non-reserved (if configured)
preprocessed word in the line has a fuzzy match with the preprocessed search term
with a score at or above the threshold.

<a id="tool.fuzzy_grep.Fuzzy_grep.find_matches_in_text"></a>

#### find\_matches\_in\_text

```python
def find_matches_in_text(text: str, search_terms: list, context: int,
                         threshold: int) -> list
```

Searches the given text and returns a list of tuples (line_number, line_content, is_central_match)
for lines that match all search terms.

<a id="tool.fuzzy_grep.Fuzzy_grep.find_matches_in_file"></a>

#### find\_matches\_in\_file

```python
def find_matches_in_file(file_path: str, search_terms: list, context: int,
                         threshold: int) -> list
```

Reads the file and returns a list of tuples (line_number, line_content, is_central_match)
for lines that match all search terms.

<a id="tool.fuzzy_grep.Fuzzy_grep.search"></a>

#### search

```python
def search(text: str = None,
           files: list = None,
           directory: str = None,
           search_terms: list = None,
           context: int = 0,
           threshold: int = 70) -> dict
```

Searches for fuzzy matches based on search_terms.

Provide one of the following inputs:
  - text: a string to search.
  - files: a list of file paths.
  - directory: a directory whose files (non-recursively) are to be searched.

Returns a dictionary with keys being either "text" or file paths, and values as a list of
(line_number, line_content, is_central_match) tuples.

<a id="tool.tests.test_fuzzy_grep_simple"></a>

# tool.tests.test\_fuzzy\_grep\_simple

<a id="tool.tests.test_equiv_check"></a>

# tool.tests.test\_equiv\_check

<a id="tool.tests.test_equiv_check.prepare_checker"></a>

#### prepare\_checker

```python
@pytest.fixture
def prepare_checker()
```

Fixture to instantiate the checker and ensure a clean workspace before each test.

<a id="tool.tests.test_equiv_check.test_setup_failure"></a>

#### test\_setup\_failure

```python
def test_setup_failure(prepare_checker)
```

Tests setup with an invalid Yosys path, expecting failure and proper error message.

<a id="tool.tests.test_equiv_check.test_setup_success"></a>

#### test\_setup\_success

```python
def test_setup_success(prepare_checker, monkeypatch)
```

Tests setup with a mocked 'yosys -V' call that simulates success.

<a id="tool.tests.test_equiv_check.test_no_module"></a>

#### test\_no\_module

```python
def test_no_module(prepare_checker)
```

If no module is found, a ValueError is raised.

<a id="tool.tests.test_equiv_check.test_multiple_modules"></a>

#### test\_multiple\_modules

```python
def test_multiple_modules(prepare_checker)
```

If more than one module is found, a ValueError is raised.

<a id="tool.tests.test_equiv_check.test_equiv_mocked_equivalent"></a>

#### test\_equiv\_mocked\_equivalent

```python
def test_equiv_mocked_equivalent(prepare_checker, monkeypatch)
```

Tests a scenario where the standard equivalence method immediately succeeds.

<a id="tool.tests.test_equiv_check.test_equiv_mocked_not_equiv"></a>

#### test\_equiv\_mocked\_not\_equiv

```python
def test_equiv_mocked_not_equiv(prepare_checker, monkeypatch)
```

Tests a scenario where the standard equivalence method fails with an assert,
proving non-equivalence.

<a id="tool.tests.test_chisel2v_simple"></a>

# tool.tests.test\_chisel2v\_simple

Example usage of the Chisel2v tool.

This script shows how one might invoke the Chisel2v class to convert
a Chisel module (given as a string) into Verilog.

<a id="tool.tests.test_chisel2v"></a>

# tool.tests.test\_chisel2v

<a id="tool.tests.test_fuzzy_grep"></a>

# tool.tests.test\_fuzzy\_grep

Unit tests for the Fuzzy_grep tool.

<a id="tool.tests.test_trivial_tool"></a>

# tool.tests.test\_trivial\_tool

<a id="tool.tests.test_compile_slang_simple"></a>

# tool.tests.test\_compile\_slang\_simple

<a id="tool.tests.test_react_simple"></a>

# tool.tests.test\_react\_simple

<a id="tool.equiv_check"></a>

# tool.equiv\_check

<a id="tool.equiv_check.Equiv_check"></a>

## Equiv\_check Objects

```python
class Equiv_check()
```

Equiv_check verifies logical equivalence of two Verilog designs using Yosys.

This class attempts two approaches:
  1) Standard 'equiv -assert'
  2) An SMT-based check

But we now call `yosys -p "..."` so the commands are handled by Yosys's command parser
rather than Tcl mode.

<a id="tool.equiv_check.Equiv_check.__init__"></a>

#### \_\_init\_\_

```python
def __init__()
```

Initializes the Equiv_check object:
 - yosys_installed: indicates if Yosys is available.
 - error_message: stores any error encountered.
 - equivalence_check_result: last known equivalence outcome (True/False/None).
 - counterexample_info: stores counterexample details if available.
 - timeout_seconds: defaults to 60s for Yosys calls.

<a id="tool.equiv_check.Equiv_check.setup"></a>

#### setup

```python
def setup(yosys_path: Optional[str] = None) -> bool
```

Checks if Yosys is installed, accessible, and meets the minimum version 0.4.
If yosys_path is provided, that binary is used; otherwise, the system PATH is used.

Returns True if Yosys is available and its version >= 0.4, False otherwise.

<a id="tool.equiv_check.Equiv_check.check_equivalence"></a>

#### check\_equivalence

```python
def check_equivalence(gold_code: str, gate_code: str) -> Optional[bool]
```

Checks the equivalence of two Verilog designs:
- gold_code: The 'gold' version to match
- gate_code: The 'gate' version

Both must define exactly one module each. If either file defines more or zero modules,
we raise an exception. We rename the gold top to 'gold', and the gate top to 'gate'.

**Returns**:

  True if designs are equivalent,
  False if designs are not equivalent,
  None if unknown (error or timeout).

<a id="tool.equiv_check.Equiv_check.get_error"></a>

#### get\_error

```python
def get_error() -> str
```

Returns the error message if any.

<a id="tool.equiv_check.Equiv_check.get_counterexample"></a>

#### get\_counterexample

```python
def get_counterexample() -> Optional[str]
```

Returns the stored counterexample info if available.

<a id="tool.chisel_diff_applier"></a>

# tool.chisel\_diff\_applier

<a id="tool.chisel_diff_applier.ChiselDiffApplier"></a>

## ChiselDiffApplier Objects

```python
class ChiselDiffApplier()
```

A tool to apply a unified diff to a Chisel source code snippet.

Given a diff (as a string) and a Chisel code snippet (as a string),
this class applies the changes and returns the updated code.

This implementation first tries to use a simple hunk-based replacement:
  - For each hunk, it extracts the removal lines and addition lines.
  - If the removal block (all removal lines concatenated with newlines) is found
    in the original code, it is replaced by the addition block.
If that does not succeed (for example, if the diff numbers or context do not match
exactly the original code), a fallback substitution is performed.

<a id="tool.chisel_diff_applier.ChiselDiffApplier.apply_diff"></a>

#### apply\_diff

```python
def apply_diff(diff_text: str, code_text: str) -> str
```

Applies the given diff (in unified diff format) to the code snippet.

**Arguments**:

- `diff_text` - The diff as a string.
- `code_text` - The original Chisel code as a string.
  

**Returns**:

  The updated code snippet as a string.

<a id="tool.chisel2v"></a>

# tool.chisel2v

<a id="tool.chisel2v.Chisel2v"></a>

## Chisel2v Objects

```python
class Chisel2v()
```

A tool to convert Chisel code to Verilog by invoking 'circt' (sbt).

<a id="tool.chisel2v.Chisel2v.setup"></a>

#### setup

```python
def setup(sbt_path: Optional[str] = None) -> bool
```

Verifies that sbt (and by extension circt) is installed. Returns True if found,
False otherwise. On failure, populates self.error_message and sets _is_ready=False.
Does not raise exceptions.

<a id="tool.chisel2v.Chisel2v.chisel_fix"></a>

#### chisel\_fix

```python
def chisel_fix(chisel_code: str, classname: str) -> str
```

Modifies the given chisel_code (a .scala file content) to ensure correct imports,
references, and a top-level App for generating SystemVerilog code with ChiselStage.
Returns the possibly modified string. Raises RuntimeError only on critical issues.

<a id="tool.chisel2v.Chisel2v.generate_verilog"></a>

#### generate\_verilog

```python
def generate_verilog(chisel_code: str, module_name: str) -> str
```

Generates Verilog from the given Chisel code using circt (sbt).
Raises RuntimeError on failure.
chisel_code: the text of the Chisel module
module_name: class name of the top module in the .scala file
out_verilog: the text of the Generated Verilog

