#!/bin/bash
# See LICENSE for details

# RTL Optimization Baseline Run Pipeline
# This script orchestrates all stages of the RTL optimization pipeline

set -e  # Exit on any error

# Configuration
HAGENT_EXECUTION_MODE=${HAGENT_EXECUTION_MODE:-docker}
HAGENT_CACHE_DIR=${HAGENT_CACHE_DIR:-/tmp/rtl_optimization_debug}

# Default paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INPUT_CONFIG=${1:-"${SCRIPT_DIR}/benchmark_config_example.yaml"}
OUTPUT_DIR=${2:-"${HAGENT_CACHE_DIR}/pipeline_results"}

# Create output directory
mkdir -p "$OUTPUT_DIR"

echo "========================================================================"
echo "RTL Optimization Baseline Run Pipeline"
echo "========================================================================"
echo "Execution Mode: $HAGENT_EXECUTION_MODE"
echo "Cache Dir: $HAGENT_CACHE_DIR"
echo "Input Config: $INPUT_CONFIG"
echo "Output Dir: $OUTPUT_DIR"
echo "========================================================================"

# Check if input config exists
if [ ! -f "$INPUT_CONFIG" ]; then
    echo "ERROR: Input configuration file not found: $INPUT_CONFIG"
    echo "Usage: $0 <config.yaml> [output_dir]"
    exit 1
fi

# Stage naming function
get_output_file() {
    local stage=$1
    echo "${OUTPUT_DIR}/step_${stage}_output.yaml"
}

# Run stage function with error handling
run_stage() {
    local stage_num=$1
    local stage_name=$2
    local script_name=$3
    local input_file=$4
    local output_file=$5

    echo ""
    echo "----------------------------------------"
    echo "Stage ${stage_num}: ${stage_name}"
    echo "----------------------------------------"
    echo "Input:  $input_file"
    echo "Output: $output_file"
    echo "Script: $script_name"

    start_time=$(date +%s)

    if HAGENT_EXECUTION_MODE=$HAGENT_EXECUTION_MODE uv run python "${SCRIPT_DIR}/${script_name}" "$input_file" -o "$output_file"; then
        end_time=$(date +%s)
        duration=$((end_time - start_time))
        echo "✓ Stage ${stage_num} completed successfully in ${duration}s"
    else
        echo "✗ Stage ${stage_num} failed!"
        echo "Check logs in: $HAGENT_CACHE_DIR"
        exit 1
    fi
}

# Pipeline execution
echo ""
echo "Starting RTL Optimization Pipeline..."

# Stage 01: Extract RTL
run_stage "01" "Extract RTL" "step_01_extract_rtl.py" \
    "$INPUT_CONFIG" "$(get_output_file "01")"

# Stage 02: Create Top Module
run_stage "02" "Create Top Module" "step_02_create_top.py" \
    "$(get_output_file "01")" "$(get_output_file "02")"

# Stage 03: Split Modules
run_stage "03" "Split Modules" "step_03_split_modules.py" \
    "$(get_output_file "02")" "$(get_output_file "03")"

# Stage 04: Synthesize Original
run_stage "04" "Synthesize Original" "step_04_synthesize.py" \
    "$(get_output_file "03")" "$(get_output_file "04")"

# Stage 05: Timing Analysis
run_stage "05" "Timing Analysis" "step_05_timing_analysis.py" \
    "$(get_output_file "04")" "$(get_output_file "05")"

# Stage 06: Generate YAML for Optimization
run_stage "06" "Generate YAML for Optimization" "step_06_generate_yamls.py" \
    "$(get_output_file "05")" "$(get_output_file "06")"

# Stage 07: Optimize Modules
run_stage "07" "Optimize Modules" "step_07_optimize_modules.py" \
    "$(get_output_file "06")" "$(get_output_file "07")"

# Stage 08: Compare Timing
run_stage "08" "Compare Timing" "step_08_compare_timing.py" \
    "$(get_output_file "07")" "$(get_output_file "08")"

echo ""
echo "========================================================================"
echo "Pipeline completed successfully!"
echo "========================================================================"
echo "Final results: $(get_output_file "08")"
echo "Debug data: $HAGENT_CACHE_DIR"
echo "Pipeline outputs: $OUTPUT_DIR"

# Display summary from final YAML
if command -v python3 &> /dev/null; then
    echo ""
    echo "Summary of Results:"
    echo "==================="
    python3 -c "
import yaml
import sys
try:
    with open('$(get_output_file "08")', 'r') as f:
        data = yaml.safe_load(f)
    metrics = data.get('metrics', {})
    print(f'Benchmark: {data.get(\"benchmark\", {}).get(\"name\", \"Unknown\")}')
    print(f'Execution Time: {metrics.get(\"total_execution_time\", \"Unknown\")}s')
    print(f'Original Slack: {metrics.get(\"original_slack\", \"Unknown\")}')
    print(f'Original Frequency: {metrics.get(\"original_frequency\", \"Unknown\")}')
    print(f'Modules Optimized: {len(metrics.get(\"modules_optimized\", []))}')
except Exception as e:
    print(f'Could not parse results: {e}')
"
fi

echo "========================================================================"
