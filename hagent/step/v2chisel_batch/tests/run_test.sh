#!/bin/bash

# Test script for v2chisel_batch
# This script can be run by anyone to test the v2chisel_batch functionality

set -e  # Exit on any error

echo "🧪 Testing v2chisel_batch..."

# Check if we're in the right directory
if [ ! -f "hagent/step/v2chisel_batch/v2chisel_batch.py" ]; then
    echo "❌ Please run this script from the hagent root directory"
    echo "   Current directory: $(pwd)"
    echo "   Expected to find: hagent/step/v2chisel_batch/v2chisel_batch.py"
    exit 1
fi

# Set environment variables if not already set
if [ -z "$AWS_BEARER_TOKEN_BEDROCK" ]; then
    echo "⚠️  AWS_BEARER_TOKEN_BEDROCK not set - LLM calls will fail"
    echo "   Set it with: export AWS_BEARER_TOKEN_BEDROCK=<your-token>"
fi

if [ -z "$AWS_DEFAULT_REGION" ]; then
    export AWS_DEFAULT_REGION=us-east-1
    echo "📍 Set AWS_DEFAULT_REGION=us-east-1"
fi

# Create output directory
mkdir -p output

echo "🚀 Running v2chisel_batch test..."

# Run the test
uv run python3 hagent/step/v2chisel_batch/v2chisel_batch.py \
    -o output/test_output.yaml \
    hagent/step/v2chisel_batch/tests/test_input.yaml

echo "✅ Test completed!"
echo "📄 Output saved to: output/test_output.yaml"

# Show summary if output exists
if [ -f "output/test_output.yaml" ]; then
    echo ""
    echo "📊 Test Results Summary:"
    echo "========================"
    # Extract key metrics from the output
    grep -E "(total_bugs|module_finder_successes|llm_successes)" output/test_output.yaml || echo "  (No detailed metrics found)"
    echo ""
    echo "🔍 Full results available in: output/test_output.yaml"
else
    echo "❌ Output file not created - check for errors above"
fi