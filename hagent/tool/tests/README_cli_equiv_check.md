# CLI Equivalence Checker

A comprehensive command-line tool for checking logical equivalence between multiple Verilog files.

## Usage

```bash
uv run python ./hagent/tool/tests/cli_equiv_check.py -r gold1.v -r gold2.v -i test1.v
```

## Options

- `-r, --reference`: Gold/reference Verilog files (can specify multiple times)
- `-i, --implementation`: Gate/implementation Verilog files (can specify multiple times)  
- `--top`: Specify a particular top module name to check (optional)
- `-v, --verbose`: Enable verbose output
- `--yosys-path`: Path to yosys binary (optional)

## Features

### Multi-File Support
- **Multiple reference files**: Combine multiple gold/reference Verilog files
- **Multiple implementation files**: Combine multiple gate/implementation Verilog files
- **Wildcard patterns**: Use shell wildcards like `ref/*.v` or `impl*.v`

### Smart Module Matching
- **IO-based matching**: Modules are matched based on compatible IO signatures
- **Different names allowed**: `adder` in gold can match `add_impl` in gate if IOs are compatible
- **Multiple modules**: Each gold module finds a matching gate module
- **Extra gate modules**: Gate design can have additional untested modules

### Comprehensive Results
- **Detailed progress**: Shows which module pairs are being checked
- **Stop on first failure**: Reports counterexample immediately when mismatch found
- **Signal-level details**: Shows exact input/output values that demonstrate non-equivalence

## Examples

### Basic Usage
```bash
# Single files
uv run python ./hagent/tool/tests/cli_equiv_check.py -r reference.v -i implementation.v

# Multiple gold files, single implementation
uv run python ./hagent/tool/tests/cli_equiv_check.py -r gold1.v -r gold2.v -i test.v

# Single gold, multiple implementations  
uv run python ./hagent/tool/tests/cli_equiv_check.py -r gold.v -i impl1.v -i impl2.v
```

### Using Wildcards
```bash
# All reference files vs all implementation files
uv run python ./hagent/tool/tests/cli_equiv_check.py -r 'ref/*.v' -i 'impl/*.v'

# Pattern matching
uv run python ./hagent/tool/tests/cli_equiv_check.py -r 'gold*.v' -i 'test*.v'
```

### Specific Module Testing
```bash
# Only check the 'adder' module
uv run python ./hagent/tool/tests/cli_equiv_check.py -r gold.v -i impl.v --top adder

# Verbose output for debugging
uv run python ./hagent/tool/tests/cli_equiv_check.py -r gold.v -i impl.v --verbose
```

## Output

### Successful Equivalence
```
Reading gold/reference files...
Reading gate/implementation files...
Setting up equivalence checker...
Running equivalence check...
Checking equivalence: adder ↔ add_impl
Checking equivalence: multiplier ↔ mult_impl  
✓ SUCCESS: All modules are equivalent!
```

### Non-Equivalent Designs
```
Reading gold/reference files...
Reading gate/implementation files...  
Setting up equivalence checker...
Running equivalence check...
Checking equivalence: adder ↔ add_impl
✗ FAILURE: Designs are NOT equivalent!

Counterexample:
================================================================================
Module pair adder↔add_impl:
  Time Signal Name             Dec       Hex           Bin
  ---- --------------- ----------- --------- -------------
     1 \gate_sum               507       1fb     111111011
     1 \gold_sum               261       105     100000101
     1 \in_a                   128        80      10000000
     1 \in_b                   133        85      10000101
     1 \trigger                  1         1             1
================================================================================
```

## Exit Codes

- `0`: All modules are equivalent
- `1`: Non-equivalent designs found or error occurred
- `2`: Inconclusive result (timeout, etc.)

## Test Files

The repository includes example test files in `hagent/tool/tests/test_files/`:

- `gold1.v`: Reference adder module
- `gold2.v`: Reference multiplier module  
- `test1.v`: Correct implementations of both modules
- `bad_impl.v`: Incorrect implementation (subtracts instead of adds)

## Running Tests

```bash
# Run all CLI tests
uv run pytest ./hagent/tool/tests/test_cli_equiv_check.py -v

# Test specific functionality
uv run pytest ./hagent/tool/tests/test_cli_equiv_check.py::test_cli_equivalent_designs -v
```