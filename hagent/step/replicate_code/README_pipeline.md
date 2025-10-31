# RTL Optimization Baseline Run Pipeline

This directory contains a comprehensive pipeline for running baseline RTL optimization using hagent's docker system. The pipeline optimizes all modules in a design and collects detailed metrics including improved slack, frequency, token consumption, and execution time.

## Overview

The pipeline implements the functionality of `splitRTLandSynthesize.sh` from `/home/sgarg3/livehd/pass/extractor/tests/` but adapted for hagent's modular docker-based architecture. It processes RTL designs through 8 sequential steps, from RTL extraction to final timing comparison.

## Files Structure

### Core Pipeline Files
- `run_stages.sh` - Main orchestration script that runs all 8 steps sequentially
- `benchmark_config_example.yaml` - Example configuration file defining benchmark parameters
- `step_01_extract_rtl.py` through `step_08_compare_timing.py` - Individual pipeline steps

### Configuration Files
- `benchmark_config_example.yaml` - Template showing how to configure different benchmarks

### Generated Outputs
- `tests/input_yamls/` - YAML files for hagent optimization input
- `generated_yamls/` - Results from hagent optimization
- `$HAGENT_CACHE_DIR/step*_*/` - Debug data and logs for each step

## Pipeline Steps

### Step 01: Extract RTL (`step_01_extract_rtl.py`)
**Purpose**: Discover and catalog RTL files in the docker container

**Input**: Benchmark configuration YAML
**Output**: Updated YAML with file paths

**What it does**:
- Discovers Verilog/SystemVerilog files in docker container
- Lists Chisel source files (if present)
- Catalogs available RTL files for processing
- Creates debug logs with file discovery results

**Expected Results**:
- `file_paths.rtl_files`: List of RTL files found
- `file_paths.chisel_files`: List of Chisel source files
- Debug log with file discovery statistics

### Step 02: Create Top Module (`step_02_create_top.py`)
**Purpose**: Use Yosys to create a clean top module file

**Input**: YAML with RTL file paths
**Output**: YAML with top module file path

**What it does**:
- Uses Yosys to extract and clean the top module
- Creates `/tmp/rtl_single/<top_module>.v`
- Verifies file creation and gets statistics

**Expected Results**:
- `file_paths.top_module_file`: Path to cleaned top module
- `file_paths.rtl_single_dir`: Directory containing top module
- Yosys execution logs and file verification

### Step 03: Split Modules (`step_03_split_modules.py`)
**Purpose**: Use LiveHD to split the top module into individual module files

**Input**: YAML with top module file
**Output**: YAML with split module files

**What it does**:
- Builds LiveHD in docker container
- Runs `inou.liveparse` to split modules
- Creates individual `.v` files in `/tmp/rtl_modules/liveparse/`

**Expected Results**:
- `file_paths.rtl_modules_dir`: Directory with split modules
- `file_paths.split_module_files`: List of individual module files
- LiveHD build and liveparse execution logs

### Step 04: Synthesize Original (`step_04_synthesize.py`)
**Purpose**: Synthesize the original design using Yosys to get baseline

**Input**: YAML with top module file
**Output**: YAML with synthesis results

**What it does**:
- Creates SDC timing constraints
- Runs Yosys synthesis with liberty library
- Generates synthesized netlist for timing analysis

**Expected Results**:
- `file_paths.synth_file`: Synthesized netlist file
- `file_paths.sdc_file`: Timing constraints file
- Yosys synthesis logs and statistics

### Step 05: Timing Analysis (`step_05_timing_analysis.py`)
**Purpose**: Run OpenSTA timing analysis to get baseline metrics

**Input**: YAML with synthesis results
**Output**: YAML with baseline timing metrics

**What it does**:
- Creates OpenSTA TCL script
- Runs timing analysis on synthesized design
- Extracts arrival time, slack, and frequency

**Expected Results**:
- `metrics.original_arrival_time`: Baseline arrival time (ns)
- `metrics.original_slack`: Baseline slack (ns)
- `metrics.original_frequency`: Baseline frequency (MHz)
- Timing reports and OpenSTA logs

### Step 06: Generate YAMLs (`step_06_generate_yamls.py`)
**Purpose**: Create YAML input files for hagent optimization

**Input**: YAML with split modules
**Output**: YAML with optimization input files

**What it does**:
- Reads each split module file
- Creates hagent-compatible YAML files with optimization prompts
- Stores YAML files in `input_yamls_dir` for processing

**Expected Results**:
- `file_paths.generated_yamls`: List of YAML files for optimization
- Individual YAML files in `tests/input_yamls/`
- Debug logs showing YAML generation statistics

### Step 07: Optimize Modules (`step_07_optimize_modules.py`)
**Purpose**: Run hagent replicate_code on each module for optimization

**Input**: YAML with optimization input files
**Output**: YAML with optimization results

**What it does**:
- Calls `hagent/step/replicate_code/replicate_code.py` for each module
- Tracks token usage and execution time
- Stores optimized modules and logs

**Expected Results**:
- `metrics.modules_optimized`: Detailed optimization results per module
- `metrics.total_tokens_used`: Total tokens consumed
- Optimized module files `*_optimized_*.v` in results directories
- Individual optimization logs for each module

### Step 08: Compare Timing (`step_08_compare_timing.py`)
**Purpose**: Synthesize optimized design and compare with baseline

**Input**: YAML with optimization results
**Output**: Final YAML with complete metrics

**What it does**:
- Replaces original modules with optimized versions
- Synthesizes the optimized design
- Runs timing analysis on optimized design
- Calculates improvements

**Expected Results**:
- `metrics.optimized_arrival_time`: Optimized arrival time (ns)
- `metrics.optimized_slack`: Optimized slack (ns)
- `metrics.optimized_frequency`: Optimized frequency (MHz)
- `metrics.*_improvement`: Improvement metrics
- `metrics.total_execution_time`: Total pipeline time

## Usage

### Basic Usage
```bash
# Set execution mode and cache directory
export HAGENT_EXECUTION_MODE=docker
export HAGENT_CACHE_DIR=/tmp/rtl_optimization_debug

# Run the complete pipeline
cd /home/sgarg3/hagent/hagent/step/replicate_code/
./run_stages.sh benchmark_config_example.yaml
```

### Custom Configuration
```bash
# Create custom configuration
cp benchmark_config_example.yaml my_benchmark.yaml
# Edit my_benchmark.yaml with your benchmark settings

# Run with custom config
./run_stages.sh my_benchmark.yaml /path/to/custom/output
```

### Individual Step Execution
```bash
# Run individual steps for debugging
HAGENT_EXECUTION_MODE=docker uv run python step_01_extract_rtl.py input.yaml -o step01_output.yaml
HAGENT_EXECUTION_MODE=docker uv run python step_02_create_top.py step01_output.yaml -o step02_output.yaml
# ... and so on
```

## Configuration

### Benchmark Configuration (`benchmark_config_example.yaml`)

The configuration file defines all parameters needed for the pipeline:

```yaml
benchmark:
  name: "PipelineDino"           # Benchmark identifier
  top_module: "PipelinedCPU"     # Top module name
  design_type: "CPU"             # Design category

docker:
  image: "mascucsc/hagent-simplechisel:2025.08"  # Docker image
  rtl_path: "/code/workspace/build/build_pipelined_d"  # RTL files location
  chisel_path: "/repo/src/main/scala"           # Chisel source location

tools:
  liberty_file: "/home/sgarg3/livehd/sky130_fd_sc_hd__ff_100C_1v95.lib"
  livehd_path: "~/livehd/"
  opensta_path: "~/opensta/OpenSTA/app/sta"
  yosys_cmd: "yosys"

optimization:
  model: "openai/o3-mini-2025-01-31"  # LLM model for optimization
  threshold: 40                        # Model-specific parameters
```

## Output Structure

### Final Metrics
After completion, the final YAML contains comprehensive metrics:

```yaml
metrics:
  # Timing metrics
  original_arrival_time: 8.45      # ns
  original_slack: -2.15            # ns
  original_frequency: 118.3        # MHz
  optimized_arrival_time: 7.82     # ns
  optimized_slack: -1.52           # ns
  optimized_frequency: 127.9       # MHz

  # Improvements
  arrival_time_improvement: 0.63   # ns saved
  slack_improvement: 0.63          # ns improved
  frequency_improvement: 9.6       # MHz gained

  # Resource usage
  total_tokens_used: 25000         # Total LLM tokens
  total_execution_time: 1847.2     # Total seconds

  # Per-module results
  modules_optimized: [...]         # Detailed per-module data
```

### Debug Data Structure
Debug data is organized by step in `$HAGENT_CACHE_DIR`:

```
$HAGENT_CACHE_DIR/
├── step01_extract_rtl_<timestamp>/
│   └── execution_log.txt
├── step02_create_top_<timestamp>/
│   └── execution_log.txt
├── step03_split_modules_<timestamp>/
│   └── execution_log.txt
├── step04_synthesize_<timestamp>/
│   ├── execution_log.txt
│   └── synthesis_log.txt
├── step05_timing_analysis_<timestamp>/
│   ├── execution_log.txt
│   ├── timing_report.rpt
│   └── run_sta.tcl
├── step06_generate_yamls_<timestamp>/
│   └── execution_log.txt
├── step07_optimize_modules_<timestamp>/
│   └── execution_log.txt
└── step08_compare_timing_<timestamp>/
    ├── execution_log.txt
    └── timing_report_optimized.rpt
```

## Environment Variables

### Required
- `HAGENT_EXECUTION_MODE=docker` - Use docker execution mode

### Optional
- `HAGENT_CACHE_DIR` - Directory for debug data (default: `/tmp/rtl_optimization_debug`)
- `OPENAI_API_KEY` - Required for LLM optimization

## Troubleshooting

### Common Issues

1. **Docker image not found**
   - Verify the docker image name in configuration
   - Ensure docker is running and image is available

2. **Liberty file not found**
   - Check the liberty file path in configuration
   - Ensure the file exists in the docker container

3. **LiveHD build fails**
   - Check LiveHD path in configuration
   - Verify bazel is available in docker

4. **OpenSTA timing analysis fails**
   - Verify OpenSTA path in configuration
   - Check SDC file format and constraints

5. **Hagent optimization fails**
   - Verify OPENAI_API_KEY is set
   - Check model name in configuration
   - Review individual module logs for errors

### Debug Information

Each step creates detailed logs in `$HAGENT_CACHE_DIR`. Check:
- `execution_log.txt` - Step execution summary
- Individual tool logs (synthesis_log.txt, timing reports, etc.)
- Return codes and error messages

### Performance Notes

- Total pipeline time depends on number of modules and LLM response time
- Token usage varies by module complexity and model choice
- Docker execution provides consistent, reproducible results
- Use `HAGENT_CACHE_DIR` on fast storage for better performance

## Extending the Pipeline

### Adding New Steps
1. Create `step_XX_name.py` following the existing pattern
2. Inherit from `hagent.core.step.Step`
3. Update `run_stages.sh` to include the new step
4. Add configuration parameters to YAML schema

### Supporting New Benchmarks
1. Create new configuration YAML
2. Ensure docker image contains required tools
3. Verify file paths match the actual benchmark layout
4. Test with a small subset first

### Customizing Optimization
1. Modify prompts in `step_06_generate_yamls.py`
2. Adjust model parameters in configuration
3. Add custom optimization constraints
4. Extend metrics collection as needed