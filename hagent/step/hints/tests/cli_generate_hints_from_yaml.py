#!/usr/bin/env python3
"""
Standalone hint generation CLI from YAML input.

This script takes a YAML file with bug information and generates hints
using the complete multi-strategy pipeline.

Usage:
    uv run python hagent/step/hints/tests/cli_generate_hints_from_yaml.py <input.yaml>

Input YAML Format:
    verilog_file: "ALU.sv"
    verilog_module: "ALU"
    unified_diff: |
      --- a/ALU.v
      +++ b/ALU.v
      @@ -10,1 +10,1 @@
      -  result = a + b;
      +  result = a - b;

    # Docker settings (script will start/stop container automatically)
    docker_patterns:  # Paths to scan in Docker
      - "/code/workspace/repo/src/main/scala"
    docker_image: "mascucsc/hagent-simplechisel:2025.09r"  # Docker image

    # Optional
    repo_path: "."  # For git commit tracking
"""

import sys
import os
import yaml
from pathlib import Path
from typing import Dict, Any

# Set execution mode to docker if not already set
if 'HAGENT_EXECUTION_MODE' not in os.environ:
    os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from hagent.step.hints.span_index import SpanIndex
from hagent.step.hints.models import DiffInfo
from hagent.step.hints.module_finder_strategy import ModuleFinder
from hagent.step.hints.source_locator import SourceLocator
from hagent.step.hints.fuzzy_grep_strategy import FuzzyGrepStrategy
from hagent.step.hints.unifier import HintUnifier
from hagent.inou.builder import Builder


def print_section(title: str):
    """Print a section header."""
    print('\n' + '=' * 70)
    print(f'  {title}')
    print('=' * 70)


def load_input_yaml(yaml_path: str) -> Dict[str, Any]:
    """Load and validate input YAML file."""
    yaml_file = Path(yaml_path)
    if not yaml_file.exists():
        raise FileNotFoundError(f'Input file not found: {yaml_path}')

    with open(yaml_file, 'r') as f:
        data = yaml.safe_load(f)

    # Validate required fields
    required = ['verilog_file', 'verilog_module', 'unified_diff']
    for field in required:
        if field not in data:
            raise ValueError(f'Missing required field in YAML: {field}')

    # Ensure docker_patterns is present for docker mode
    if 'docker_patterns' not in data:
        data['docker_patterns'] = ['/code/workspace/repo/src/main/scala']  # Default

    return data


def generate_hints(input_data: Dict[str, Any]) -> None:
    """Run the complete hint generation pipeline."""

    print_section('INPUT DATA')
    print(f'\nVerilog File: {input_data["verilog_file"]}')
    print(f'Verilog Module: {input_data["verilog_module"]}')

    print('\nUnified Diff:')
    print('-' * 70)
    print(input_data['unified_diff'])
    print('-' * 70)

    # Initialize Builder and Docker container
    docker_image = input_data.get('docker_image', 'mascucsc/hagent-simplechisel:2025.09r')
    print('\n🐳 Step 0: Initializing Docker Container')
    print(f'   Docker image: {docker_image}')

    builder = Builder(docker_image=docker_image)

    try:
        # Setup builder (starts docker container)
        if not builder.setup():
            raise RuntimeError(f'Failed to setup Builder: {builder.get_error()}')

        # Get actual container name
        docker_container = None
        if builder.runner and builder.runner.container_manager and builder.runner.container_manager.container:
            docker_container = builder.runner.container_manager.container.name
            print(f'   ✅ Docker container started: {docker_container}')
        else:
            raise RuntimeError('Failed to start docker container')

        _run_hints_pipeline(input_data, builder, docker_container)

    finally:
        # Always cleanup docker container
        print('\n🧹 Cleaning up Docker container...')
        builder.cleanup()
        print('   ✅ Docker container stopped and cleaned up')


def _run_hints_pipeline(input_data: Dict[str, Any], builder: Builder, docker_container: str) -> None:
    """Run the actual hints generation pipeline (separated for cleanup handling)."""

    # Step 1: Build Span Index
    print_section('STEP 1: Building Span Index')
    print('Parsing Chisel/Scala files...')

    # Scan docker for Scala files
    print('🔍 Scanning Docker container for Scala files...')
    docker_patterns = input_data.get('docker_patterns', ['/code/workspace/repo/src/main/scala'])

    expanded_files = []
    for docker_path in docker_patterns:
        # List files in docker using builder
        try:
            import subprocess

            result = subprocess.run(
                ['docker', 'exec', docker_container, 'find', docker_path, '-name', '*.scala'],
                capture_output=True,
                text=True,
                check=True,
            )
            docker_files = result.stdout.strip().split('\n')
            for file_path in docker_files:
                if file_path:  # Skip empty lines
                    expanded_files.append(f'docker:{docker_container}:{file_path}')
        except subprocess.CalledProcessError as e:
            print(f'   ⚠️  Failed to list files in {docker_path}: {e}')

    print(f'\nFiles to parse: {len(expanded_files)}')
    for i, f in enumerate(expanded_files[:10], 1):
        print(f'  {i}. {f}')
    if len(expanded_files) > 10:
        print(f'  ... and {len(expanded_files) - 10} more')

    span_index = SpanIndex(builder=builder, repo_path=input_data.get('repo_path'))
    span_index.build(expanded_files)

    print(f'\n✅ Index built: {span_index}')
    print(f'\nModules found: {len(span_index)}')

    # Show top 10 modules
    all_modules = span_index.get_all_modules()
    for i, module in enumerate(all_modules[:10], 1):
        print(f'  {i}. {module.name} ({module.span_type}) - lines {module.start_line}-{module.end_line}')
    if len(all_modules) > 10:
        print(f'  ... and {len(all_modules) - 10} more')

    # Step 2: Create DiffInfo
    print_section('STEP 2: Creating DiffInfo')

    diff_info = DiffInfo(
        verilog_file=input_data['verilog_file'],
        verilog_module=input_data['verilog_module'],
        unified_diff=input_data['unified_diff'],
    )

    print('\n✅ DiffInfo created')
    print(f'   Module: {diff_info.verilog_module}')
    print(f'   File: {diff_info.verilog_file}')
    print(f'   Changed lines: {diff_info.changed_lines if diff_info.changed_lines else "(none detected)"}')

    # Step 3: Initialize Strategies
    print_section('STEP 3: Initializing Strategies')

    strategies = [
        ModuleFinder(min_confidence=0.3),
        SourceLocator(),
        FuzzyGrepStrategy(threshold=70),
    ]

    print('\nStrategies:')
    for s in strategies:
        print(f'  - {s.name}')

    # Step 4: Run Pipeline
    print_section('STEP 4: Running Hint Generation Pipeline')

    unifier = HintUnifier(span_index, strategies)
    candidates = unifier.run_and_aggregate(diff_info, builder=builder)

    # Step 5: Display Results
    print_section('STEP 5: RESULTS - Module Candidates')

    if not candidates:
        print('\n⚠️  No candidates found!')
        print('\nPossible reasons:')
        print('  - Module name mismatch between Verilog and Chisel')
        print('  - No matching identifiers found in diff')
        print('  - Chisel files not parsed correctly')
        return

    print(f'\n✅ Found {len(candidates)} candidate modules')
    print('\nRanked by fused confidence score:\n')

    for i, candidate in enumerate(candidates, 1):
        tier = candidate.get_tier()
        tier_emoji = {'high': '🟢', 'medium': '🟡', 'low': '🟠', 'none': '⚪'}[tier]

        print(f'{tier_emoji} #{i}. {candidate.span.name} ({candidate.span.span_type})')
        print(f'   File: {candidate.span.file}')
        print(f'   Lines: {candidate.span.start_line}-{candidate.span.end_line}')
        print(f'   Fused Score: {candidate.fused_score:.3f} (tier: {tier})')
        print(f'   Sources Hit: {candidate.sources_hit}/3')
        print('   Per-Source Scores:')

        source_names = {'mf': 'ModuleFinder', 'sl': 'SourceLocator', 'fg': 'FuzzyGrep'}
        for source_key, score in candidate.scores.items():
            source_name = source_names.get(source_key, source_key)
            print(f'      • {source_name:20s}: {score:.3f}')

        # Show evidence details
        print('   Evidence:')
        for hint in candidate.all_evidence:
            print(f'      • {hint.source}: confidence={hint.confidence:.3f}')
            if hint.evidence:
                for key, value in list(hint.evidence.items())[:3]:  # Show first 3 keys
                    print(f'         - {key}: {value}')

        print()

    # Step 6: Recommendation
    print_section('STEP 6: Recommendation')

    top_candidate = candidates[0]
    print(f'\n🎯 Top candidate: {top_candidate.span.name}')
    print(f'   Confidence: {top_candidate.fused_score:.3f}')
    print(f'   Tier: {top_candidate.get_tier()}')
    print(f'   Location: {top_candidate.span.file}:{top_candidate.span.start_line}-{top_candidate.span.end_line}')

    if top_candidate.fused_score >= 0.95:
        print('\n✅ HIGH CONFIDENCE - This is very likely the correct module to fix!')
    elif top_candidate.fused_score >= 0.70:
        print('\n🟡 MEDIUM CONFIDENCE - This module is a good candidate to try.')
    elif top_candidate.fused_score >= 0.50:
        print('\n🟠 LOW CONFIDENCE - Consider trying this module, but confidence is low.')
    else:
        print('\n⚪ VERY LOW CONFIDENCE - Results may not be reliable.')

    print_section('HINT GENERATION COMPLETED ✅')


def main():
    """Main entry point."""
    if len(sys.argv) != 2:
        print('Usage: uv run python hagent/step/hints/tests/cli_generate_hints_from_yaml.py <input.yaml>')
        print('\nExample input.yaml:')
        print("""
verilog_file: "ALU.sv"
verilog_module: "ALU"
unified_diff: |
  --- a/ALU.v
  +++ b/ALU.v
  @@ -10,1 +10,1 @@
  -  result = a + b;
  +  result = a - b;

# Docker settings (script will start/stop container automatically)
docker_patterns:
  - "/code/workspace/repo/src/main/scala"
docker_image: "mascucsc/hagent-simplechisel:2025.09r"

# Optional
repo_path: "."
        """)
        sys.exit(1)

    yaml_path = sys.argv[1]

    try:
        print('=' * 70)
        print('  Multi-Strategy Hint Generation from YAML')
        print('=' * 70)
        print(f'\nInput file: {yaml_path}')

        input_data = load_input_yaml(yaml_path)
        generate_hints(input_data)

    except Exception as e:
        print(f'\n❌ ERROR: {e}')
        import traceback

        traceback.print_exc()
        sys.exit(1)


if __name__ == '__main__':
    main()
