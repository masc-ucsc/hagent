# V2ChiselFix

V2ChiselFix is a step in the hardware design automation pipeline that refines Chisel code based on Logic Equivalence Check (LEC) results. It leverages a Language Model (LLM) to iteratively improve Chisel code when discrepancies are found between generated Verilog and the fixed Verilog specifications.

## Table of Contents
- Features
- Usage
  - Running the Pass
- Input and Output
  - Input YAML Structure
  - Output YAML Structure
- Configuration
  - LLM Configuration
  - Iteration Limit
- Testing
- Troubleshooting
- Contributing
- License

## Features
- **Logic Equivalence Check (LEC)**: Ensures that the Verilog generated from Chisel code matches the fixed Verilog specifications.
- **Iterative Refinement**: Uses an LLM to iteratively refine Chisel code when LEC detects discrepancies.
- **Single Chat Session with LLM**: Maintains a single conversation context with the LLM across iterations to leverage historical feedback.
- **Automated Verilog Generation**: Converts refined Chisel code into Verilog using Chisel2v.

## Usage

### Running the Pass
Execute the `v2chisel_fix` pass using the following command:
```bash
uv run python3 hagent/step/v2chisel_fix/v2chisel_fix.py -o hagent/step/v2chisel_fix/out2.yaml hagent/step/v2chisel_pass1/out2.yaml
```
- `uv run`: Executes the command within the uv-managed virtual environment.
- `python3 hagent/step/v2chisel_fix/v2chisel_fix.py`: Runs the v2chisel_fix script.
- `-o hagent/step/v2chisel_fix/out2.yaml`: Specifies the output YAML file where results will be written.
- `hagent/step/v2chisel_pass1/out2.yaml`: Specifies the input YAML file generated from the previous step (`v2chisel_pass1`).

## Input and Output

### Input YAML Structure
The input YAML file (`hagent/step/v2chisel_pass1/out2.yaml`) should contain the following fields:
- **chisel_pass1**:
  - `chisel_changed`: The initial Chisel code snippet to be checked or refined.
  - `verilog_candidate`: The Verilog code generated from the Chisel code.
  - `was_valid`: Boolean indicating if the initial Verilog was considered valid.
- **verilog_fixed**:
  - The reference Verilog code against which the candidate will be checked.
- **llm**:
  - Configuration for the Language Model (e.g., model name, API keys).

#### Example
```yaml
chisel_pass1:
  chisel_changed: |
    class MyModule extends Module {
      val io = IO(new Bundle {})
    }
  verilog_candidate: |
    module mymodule(input clk, rst);
    endmodule
  was_valid: true

verilog_fixed: |
  module mymodule(input clk, rst);
    // new changes
  endmodule

llm:
  model: "test-model"
```

### Output YAML Structure
The output YAML file (`hagent/step/v2chisel_fix/out2.yaml`) will include:
- **chisel_fixed**:
  - `original_chisel`: Original Chisel code.
  - `refined_chisel`: Refined Chisel code after LEC passes.
  - `equiv_passed`: Boolean indicating if the final code passed LEC.

#### Example
```yaml
chisel_fixed:
  original_chisel: "class MyModule extends Module { val io = IO(new Bundle {}) }"
  refined_chisel: "class MyModule_attempt1 extends Module { ... }"
  equiv_passed: true
```

## Configuration

### LLM Configuration
Ensure that `prompt3.yaml` exists in the `hagent/step/v2chisel_fix/` directory and is properly formatted to interact with the LLM. The LLM configuration is provided in the input YAML under the `llm` section.

#### Example `prompt3.yaml`
```yaml
- role: system
  content: "Refinement system message"
- role: user
  content: "Please refine the following Chisel code based on the LEC error."
```

### Iteration Limit
By default, `v2chisel_fix` will attempt up to **10** refinement iterations (`lec_limit`). This can be adjusted in the `v2chisel_fix.py` script if needed.

## Testing
Run the test suite with coverage using:
```bash
uv run pytest --cov=hagent --cov-report=html -k "test_v2chisel_fix" -v
```
This command will execute all tests related to `v2chisel_fix` and generate an HTML coverage report in the `htmlcov` directory.

## Troubleshooting
- **KeyError: 'chisel_fixed'**:  
  Ensure that the `run` method always returns a dictionary containing the `chisel_fixed` key, even if an error occurs during processing.
- **AttributeError: 'V2ChiselFix' object has no attribute 'verilog_fixed'**:  
  Make sure that `self.verilog_fixed_str` is properly initialized in the `setup` method and that `verilog_fixed` is correctly passed to the LLM.
- **TypeError: string indices must be integers, not 'str'**:  
  This occurs if the LLM response is not properly formatted. Ensure that `prompt3.yaml` is correctly structured and that the LLM returns the expected format.
- **LLM Conversation Issues**:  
  Verify that the LLM maintains a single conversation context across iterations by not re-instantiating the LLM in each refinement step.

## Contributing
Contributions are welcome! Please follow these steps:
- Fork the Repository
- Create a Feature Branch:
```bash
git checkout -b feature/YourFeature
```
- Commit Your Changes:
```bash
git commit -m "Add Your Feature"
```
- Push to the Branch:
```bash
git push origin feature/YourFeature
```
- Open a Pull Request

## License
This project is licensed under the MIT License.
