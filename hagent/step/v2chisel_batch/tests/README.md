# V2chisel_batch Tests

This directory contains test files for the v2chisel_batch step.

## Quick Test

To run a quick test from the hagent root directory:

```bash
# Set up environment variables (required for LLM)
export AWS_ACCESS_KEY_ID=<your-access-key-id>
export AWS_SECRET_ACCESS_KEY=<your-secret-access-key>
export AWS_DEFAULT_REGION=us-east-1

# Run the test
bash hagent/step/v2chisel_batch/tests/run_test.sh
```

## Test Files

- `test_bug_list.yaml`: Sample bug list with 2 simple Verilog diffs
- `test_input.yaml`: Test configuration pointing to local test files
- `sample_chisel/SampleAdder.scala`: Sample Chisel code for testing module_finder
- `run_test.sh`: Automated test script
- `README.md`: This file

## Expected Behavior

The test should:
1. ✅ Load the test bug list (2 bugs: Adder.sv, Alu.sv)
2. ✅ Find local Chisel files in `sample_chisel/`
3. ✅ Run module_finder to match Verilog modules to Chisel code
4. ✅ Generate hints for LLM
5. ✅ Call LLM to generate Chisel diffs (requires AWS credentials)
6. ✅ Output results to `output/test_output.yaml`

## Troubleshooting

### "Bug list file not found"
- Make sure you're running from the hagent root directory
- Check that `hagent/step/v2chisel_batch/tests/test_bug_list.yaml` exists

### "LLM authentication error"
- Set your AWS_ACCESS_KEY_ID and AWS_SECRET_ACCESS_KEY environment variables
- Ensure AWS_DEFAULT_REGION is set (defaults to us-east-1)

### "No module matches found"
- This is expected if Docker container is not available
- The test should still complete and try metadata fallback

## Test Output

The test generates `output/test_output.yaml` with:
- Bug processing results
- Module finder statistics
- LLM generation success/failure rates
- Detailed per-bug results

## Running Without Docker

The test is designed to work without Docker by using local sample Chisel files. It will show "0 docker files found" but should still complete successfully.