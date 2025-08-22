# V2chisel_batch Retry Mechanism Test

This test demonstrates the retry mechanism for when the diff applier fails to find removal lines in the actual code.

## What the test does

1. **Tests DockerDiffApplier with wrong diff** - Uses an intentionally incorrect removal line that doesn't exist in the actual file
2. **Verifies proper error handling** - Confirms the applier correctly fails and reports missing lines  
3. **Tests with correct diff** - Uses the proper format that matches the actual file content
4. **Shows the planned retry flow** - Demonstrates how v2chisel_batch should handle applier failures

## How to run the test

```bash
# From the project root directory
uv run python3 hagent/step/v2chisel_batch/tests/test_retry_mechanism.py
```

## Expected output

```
🧪 Testing v2chisel_batch retry mechanism
============================================================
📁 Input file: .../test_input_retry.yaml
📁 Output file: .../test_output_retry.yaml
✅ V2chisel_batch initialized successfully

🐳 Testing DockerDiffApplier with intentionally wrong diff...
✅ Applier correctly failed with wrong diff

🔄 Now testing correct diff...
✅ Applier succeeded with correct diff format

🎯 Test Summary:
✅ DockerDiffApplier correctly handles both success and failure cases
🎉 Test completed successfully!
```

## Files used in test

- `test_input_retry.yaml` - Test configuration that uses the wrong bug list
- `test_bug_list_retry.yaml` - Bug list with intentionally wrong Verilog diff
- `test_retry_mechanism.py` - The actual test script

## Next steps for implementation

The test validates that the DockerDiffApplier correctly:
1. ❌ **Fails when removal lines don't match** - Returns error with specific missing lines
2. ✅ **Succeeds when removal lines match** - Applies changes correctly

Now v2chisel_batch needs to be modified to:
1. **Try applying the LLM-generated diff**
2. **If applier fails, call LLM again** with error details and retry prompt
3. **Continue the loop** until success or max retries reached
4. **After successful application, compile the code**
5. **Run Logic Equivalence Check (LEC)**

## Docker container requirement

The test requires Docker container `musing_sammet` to be running with Xiangshan code.

Check container status: `docker ps -a --filter name=musing_sammet`
Start if needed: `docker start musing_sammet`