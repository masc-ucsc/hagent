#!/bin/bash

# LEC Isolation Test Runner
# Tests LEC functionality with known correct chisel_diff

echo "🔬 Starting LEC Isolation Test..."
echo "This test bypasses the LLM and uses a known correct chisel_diff"
echo "to test the full LEC pipeline in isolation."
echo ""

cd "$(dirname "$0")"

# Run the test
python3 test_lec_isolated.py

test_result=$?

echo ""
if [ $test_result -eq 0 ]; then
    echo "🎉 LEC test PASSED! The LEC functionality works correctly."
else
    echo "💥 LEC test FAILED! There are issues with the LEC pipeline."
fi

exit $test_result