#!/bin/bash

echo "🔍 AWS Credentials Troubleshooting for v2chisel_batch"
echo "=================================================="

# Check environment variables
echo ""
echo "📋 Environment Variables:"
echo "-------------------------"
if [ -n "$AWS_BEARER_TOKEN_BEDROCK" ]; then
    echo "✅ AWS_BEARER_TOKEN_BEDROCK is set (${#AWS_BEARER_TOKEN_BEDROCK} characters)"
else
    echo "❌ AWS_BEARER_TOKEN_BEDROCK is NOT set"
    echo "   Set it with: export AWS_BEARER_TOKEN_BEDROCK=<your-token>"
fi

if [ -n "$AWS_DEFAULT_REGION" ]; then
    echo "✅ AWS_DEFAULT_REGION is set: $AWS_DEFAULT_REGION"
else
    echo "❌ AWS_DEFAULT_REGION is NOT set"
    echo "   Set it with: export AWS_DEFAULT_REGION=us-west-2"
fi

if [ -n "$AWS_REGION" ]; then
    echo "✅ AWS_REGION is set: $AWS_REGION"
else
    echo "⚠️  AWS_REGION is not set (optional, but some tools use it)"
fi

# Check AWS CLI configuration
echo ""
echo "🔧 AWS CLI Configuration:"
echo "-------------------------"
if command -v aws &> /dev/null; then
    echo "✅ AWS CLI is installed"
    aws sts get-caller-identity 2>/dev/null && echo "✅ AWS CLI can authenticate" || echo "❌ AWS CLI authentication failed"
else
    echo "⚠️  AWS CLI not found (not required for v2chisel_batch, but useful for debugging)"
fi

# Test LLM directly
echo ""
echo "🧪 Testing LLM Authentication:"
echo "------------------------------"
uv run python3 hagent/step/v2chisel_batch/tests/test_llm_simple.py

echo ""
echo "📝 Summary:"
echo "----------"
if [ -n "$AWS_BEARER_TOKEN_BEDROCK" ] && [ -n "$AWS_DEFAULT_REGION" ]; then
    echo "✅ Environment variables look correct"
    echo "   If you're still getting authentication errors, the token may be invalid or expired"
else
    echo "❌ Missing required environment variables"
    echo "   Required: AWS_BEARER_TOKEN_BEDROCK and AWS_DEFAULT_REGION"
fi

echo ""
echo "💡 Quick Fix:"
echo "   export AWS_BEARER_TOKEN_BEDROCK=<your-token>"
echo "   export AWS_DEFAULT_REGION=us-west-2"
echo "   bash hagent/step/v2chisel_batch/tests/run_test.sh"