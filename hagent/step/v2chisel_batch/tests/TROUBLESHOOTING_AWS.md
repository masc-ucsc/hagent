# AWS Bedrock Authentication Troubleshooting

## ✅ **Region Configuration Fixed**

All configuration files have been updated to use `us-west-2` region:
- `v2chisel_batch_conf.yaml`: `aws_region_name: "us-west-2"`
- Test scripts now default to `us-west-2`

## 🔍 **Troubleshooting Steps**

### 1. Check Current Configuration
```bash
bash hagent/step/v2chisel_batch/tests/check_aws_credentials.sh
```

### 2. Set Correct Environment Variables
```bash
export AWS_BEARER_TOKEN_BEDROCK=<your-token>
export AWS_DEFAULT_REGION=us-west-2
export AWS_REGION=us-west-2
```

### 3. Verify Token Format
The AWS_BEARER_TOKEN_BEDROCK should be a base64-encoded string. Example format:
```
ABSKZnJhYmllaWstYXQtNzEzNTI2OTEwNTYwOmZ0VmRaZ0dpaUZuMU1KOGZ1WFQ1Z0ZPY1h0eGdMckM2...
```

### 4. Test LLM Authentication
```bash
bash hagent/step/v2chisel_batch/tests/run_test.sh
```

## 🚨 **Common Issues**

### "BedrockException Invalid Authentication"
**Possible causes:**
1. **Wrong region**: Ensure using `us-west-2`
2. **Invalid token**: Token may be expired or malformed
3. **Missing environment variables**: Both `AWS_BEARER_TOKEN_BEDROCK` and region must be set
4. **Token permissions**: Token may not have Bedrock access permissions

### "Unable to locate credentials"
**Solutions:**
1. Check token is properly base64 encoded
2. Verify token has not expired
3. Ensure using the correct AWS account/organization token
4. Try regenerating the token

## 🔧 **Advanced Debugging**

### Enable LiteLLM Debug Mode
Add this to your script:
```bash
export LITELLM_LOG=DEBUG
```

### Check AWS CLI (if available)
```bash
aws sts get-caller-identity
aws bedrock list-foundation-models --region us-west-2
```

### Manual Token Test
```python
import boto3
import base64

# Decode your token to check format
token = "YOUR_TOKEN_HERE"
try:
    decoded = base64.b64decode(token)
    print("Token appears valid (base64 decodable)")
except:
    print("Token may be malformed")
```

## 📞 **Getting Help**

If all troubleshooting fails:
1. Verify with your AWS administrator that the token is valid
2. Check if Bedrock service is available in `us-west-2` for your account
3. Confirm the specific Llama model is accessible: `bedrock/us.meta.llama3-3-70b-instruct-v1:0`

## ✅ **Success Indicators**

When working correctly, you should see:
```
🤖 [LLM] Calling LLM (attempt 1)...
✅ LLM generated diff: XXX characters
✅ [LLM] Successfully generated Chisel diff
```

Instead of:
```
❌ [LLM] Failed to generate Chisel diff: LLM error: litellm call error: litellm.AuthenticationError
```