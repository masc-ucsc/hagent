#!/usr/bin/env python3
"""
Summarize v2chisel_batch results from output directory.

Usage:
    uv run python summarize_results.py -o <output_dir>
    uv run python summarize_results.py -o /home/farzaneh/hagent/dino/gpt-5-codex-singlecycle-A

Analyzes YAML result files and provides detailed statistics on:
- LEC success/failure rates
- Iteration counts for successes
- Failure reasons (LEC mismatch, compiler, applier, etc.)
- Hint generation success rate
"""

import argparse
from pathlib import Path
from collections import defaultdict
from ruamel.yaml import YAML


def load_yaml_file(filepath):
    """Load a YAML file and return its contents"""
    yaml = YAML()
    yaml.preserve_quotes = True
    try:
        with open(filepath, 'r') as f:
            return yaml.load(f)
    except Exception as e:
        print(f'⚠️  Warning: Failed to load {filepath}: {e}')
        return None


def extract_bug_results(data):
    """Extract bug results from YAML data structure"""
    # Check if this is a batch result file with v2chisel_batch_with_llm
    if 'v2chisel_batch_with_llm' in data:
        return data['v2chisel_batch_with_llm'].get('bug_results', [])
    # Check if this is an individual bug result file
    elif 'bug_results' in data.get('v2chisel_batch_with_llm', {}):
        return data['v2chisel_batch_with_llm']['bug_results']
    return []


def analyze_single_bug(bug_result, source_file='unknown', file_timestamp=None):
    """Analyze a single bug result and extract statistics"""

    # Extract pipeline stages
    llm_success = bug_result.get('llm_success', False)
    applier_success = bug_result.get('applier_success', False)
    compile_success = bug_result.get('compile_success', False)
    verilog_gen_success = bug_result.get('verilog_generation_success', False)
    lec_success = bug_result.get('lec_success', False)
    lec_equivalent = bug_result.get('lec_equivalent', False)

    # CRITICAL FIX: Recompute pipeline_success correctly (including LEC equivalence check)
    # Don't trust the stored value as older runs had a bug where pipeline_success=True even if LEC failed
    pipeline_success = (
        llm_success
        and applier_success
        and compile_success
        and verilog_gen_success
        and lec_equivalent  # Must pass LEC equivalence check!
    )

    # Extract the actual bug number from the filename
    # Patterns: "01_Control.yaml", "debug_bug_17.yaml", "03_ImmediateGenerator.yaml"
    import re

    bug_number = None
    if source_file:
        # Try pattern: 01_Module.yaml or 03_Module.yaml
        match = re.match(r'^(\d+)_', source_file)
        if match:
            bug_number = int(match.group(1))
        else:
            # Try pattern: debug_bug_17.yaml or test_bug_03.yaml
            match = re.search(r'bug[_-]?(\d+)', source_file)
            if match:
                bug_number = int(match.group(1))

    # If we couldn't extract from filename, fall back to bug_index from YAML
    if bug_number is None:
        bug_number = bug_result.get('bug_index', -1)

    analysis = {
        'source_file': source_file,  # Track which YAML file this bug came from
        'file_timestamp': file_timestamp,  # Track when the file was last modified
        'bug_index': bug_result.get('bug_index', -1),  # Keep original for reference
        'bug_number': bug_number,  # Actual bug number extracted from filename
        'verilog_file': bug_result.get('verilog_file', 'unknown'),
        'module_name': bug_result.get('module_name', 'unknown'),
        # Hint generation
        'has_hints': bug_result.get('has_hints', False),
        'hints_source': bug_result.get('hints_source', 'none'),
        # Pipeline stages
        'llm_success': llm_success,
        'applier_success': applier_success,
        'compile_success': compile_success,
        'verilog_gen_success': verilog_gen_success,
        'lec_success': lec_success,
        'lec_equivalent': lec_equivalent,
        'pipeline_success': pipeline_success,  # Use recomputed value
        # Error information
        'llm_error': bug_result.get('llm_error', ''),
        'applier_error': bug_result.get('applier_error', ''),
        'compile_error': bug_result.get('compile_error', ''),
        'lec_error': bug_result.get('lec_error', ''),
        'failure_stage': bug_result.get('failure_stage', 'unknown'),
        # Iteration information
        'total_attempts': bug_result.get('total_attempts', 0),
        'success_at_iteration': bug_result.get('success_at_iteration', None),
        'iteration_history': bug_result.get('iteration_history', []),
    }

    # Determine failure reason
    if analysis['pipeline_success']:
        analysis['failure_reason'] = None
    elif not analysis['has_hints']:
        analysis['failure_reason'] = 'no_hints'
    elif not analysis['llm_success']:
        analysis['failure_reason'] = 'llm_failed'
    elif not analysis['applier_success']:
        analysis['failure_reason'] = 'applier_failed'
    elif not analysis['compile_success']:
        analysis['failure_reason'] = 'compiler_failed'
    elif not analysis['verilog_gen_success']:
        analysis['failure_reason'] = 'verilog_gen_failed'
    elif analysis['lec_success'] and not analysis['lec_equivalent']:
        analysis['failure_reason'] = 'lec_mismatch'
    elif not analysis['lec_success']:
        analysis['failure_reason'] = 'lec_failed'
    else:
        analysis['failure_reason'] = 'unknown'

    return analysis


def find_yaml_files(output_dir):
    """Find all YAML files in the output directory (excluding subdirectories)"""
    yaml_files = []
    output_path = Path(output_dir)

    # Get all .yaml files in the main directory (not subdirectories)
    for yaml_file in output_path.glob('*.yaml'):
        if yaml_file.is_file():
            yaml_files.append(yaml_file)

    return sorted(yaml_files)


def find_individual_results_dirs(output_dir):
    """Find all individual_results_* directories"""
    output_path = Path(output_dir)
    return sorted([d for d in output_path.glob('individual_results_*') if d.is_dir()])


def print_summary(all_analyses, show_timestamps=False, latest_only=False):
    """Print comprehensive summary of all bug analyses"""

    # If latest_only is True, filter to only show the most recent result per test case
    if latest_only and all_analyses:
        # Group by (bug_number, verilog_file, module_name) to identify unique test cases
        test_case_groups = defaultdict(list)

        for analysis in all_analyses:
            # Create a unique key for each test case using bug_number extracted from filename
            key = (analysis['bug_number'], analysis['verilog_file'], analysis['module_name'])
            test_case_groups[key].append(analysis)

        # Keep only the most recent result for each test case
        filtered_analyses = []
        for key, analyses_list in test_case_groups.items():
            # Sort by timestamp (newest first) and take the first one
            latest = sorted(analyses_list, key=lambda x: x.get('file_timestamp', 0), reverse=True)[0]
            filtered_analyses.append(latest)

        print(f'📊 Showing LATEST results only ({len(test_case_groups)} unique test cases, {len(all_analyses)} total runs)')
        print('   Use without --latest-only to see all historical runs\n')
        all_analyses = filtered_analyses

    total_bugs = len(all_analyses)

    if total_bugs == 0:
        print('❌ No bug results found!')
        return

    # Count successes and failures
    hints_generated = sum(1 for a in all_analyses if a['has_hints'])
    llm_successes = sum(1 for a in all_analyses if a['llm_success'])
    applier_successes = sum(1 for a in all_analyses if a['applier_success'])
    compile_successes = sum(1 for a in all_analyses if a['compile_success'])
    verilog_successes = sum(1 for a in all_analyses if a['verilog_gen_success'])
    lec_successes = sum(1 for a in all_analyses if a['lec_success'])
    lec_passes = sum(1 for a in all_analyses if a['lec_equivalent'])
    pipeline_successes = sum(1 for a in all_analyses if a['pipeline_success'])

    # Count failure reasons
    failure_counts = defaultdict(int)
    for a in all_analyses:
        if a['failure_reason']:
            failure_counts[a['failure_reason']] += 1

    # Print overall summary
    print('=' * 80)
    print('📊 V2CHISEL BATCH RESULTS SUMMARY')
    print('=' * 80)
    print(f'Total Bugs Analyzed: {total_bugs}')
    print()

    print('📈 STAGE-BY-STAGE SUCCESS RATES:')
    print(f'  Hints Generated:       {hints_generated}/{total_bugs} ({hints_generated / total_bugs * 100:.1f}%)')
    print(f'  LLM Success:           {llm_successes}/{total_bugs} ({llm_successes / total_bugs * 100:.1f}%)')
    print(f'  Applier Success:       {applier_successes}/{total_bugs} ({applier_successes / total_bugs * 100:.1f}%)')
    print(f'  Compile Success:       {compile_successes}/{total_bugs} ({compile_successes / total_bugs * 100:.1f}%)')
    print(f'  Verilog Gen Success:   {verilog_successes}/{total_bugs} ({verilog_successes / total_bugs * 100:.1f}%)')
    print(f'  LEC Run Success:       {lec_successes}/{total_bugs} ({lec_successes / total_bugs * 100:.1f}%)')
    print(f'  🎯 LEC PASS (Equiv):   {lec_passes}/{total_bugs} ({lec_passes / total_bugs * 100:.1f}%)')
    print(f'  ✅ Pipeline Complete:  {pipeline_successes}/{total_bugs} ({pipeline_successes / total_bugs * 100:.1f}%)')
    print()

    print('❌ FAILURE BREAKDOWN:')
    failure_labels = {
        'no_hints': 'No Hints Generated',
        'llm_failed': 'LLM Generation Failed',
        'applier_failed': 'Applier Failed',
        'compiler_failed': 'Compiler Failed',
        'verilog_gen_failed': 'Verilog Generation Failed',
        'lec_failed': 'LEC Execution Failed',
        'lec_mismatch': 'LEC Mismatch (Not Equivalent)',
        'unknown': 'Unknown Failure',
    }
    for reason, label in failure_labels.items():
        count = failure_counts.get(reason, 0)
        if count > 0:
            print(f'  {label:30s}: {count}/{total_bugs} ({count / total_bugs * 100:.1f}%)')
    print()

    # Iteration statistics for successes
    successful_bugs = [a for a in all_analyses if a['lec_equivalent']]
    if successful_bugs:
        print(f'🔄 ITERATION STATISTICS FOR {len(successful_bugs)} SUCCESSFUL BUGS:')

        iteration_counts = defaultdict(int)
        total_attempts_sum = 0

        for bug in successful_bugs:
            success_iter = bug.get('success_at_iteration')
            if success_iter:
                iteration_counts[success_iter] += 1
            total_attempts_sum += bug.get('total_attempts', 0)

        avg_attempts = total_attempts_sum / len(successful_bugs) if successful_bugs else 0

        print(f'  Average attempts per successful bug: {avg_attempts:.2f}')
        print('  Success by iteration:')
        for iter_num in sorted(iteration_counts.keys()):
            count = iteration_counts[iter_num]
            print(f'    Iteration {iter_num}: {count} bugs ({count / len(successful_bugs) * 100:.1f}%)')
        print()

    # Module-based failure analysis
    print('=' * 80)
    print('📊 FAILURE ANALYSIS BY MODULE:')
    print('=' * 80)

    # Group failures by module
    module_failures = defaultdict(lambda: {'llm': 0, 'applier': 0, 'compiler': 0, 'lec_mismatch': 0, 'total': 0})

    for a in all_analyses:
        module = a['module_name']
        if not a['pipeline_success']:
            module_failures[module]['total'] += 1
            if a['failure_reason'] == 'llm_failed':
                module_failures[module]['llm'] += 1
            elif a['failure_reason'] == 'applier_failed':
                module_failures[module]['applier'] += 1
            elif a['failure_reason'] == 'compiler_failed':
                module_failures[module]['compiler'] += 1
            elif a['failure_reason'] == 'lec_mismatch':
                module_failures[module]['lec_mismatch'] += 1

    if module_failures:
        print(f'{"Module":20s} {"Total":6s} {"LLM":5s} {"Appl":5s} {"Comp":5s} {"LEC":5s}')
        print('-' * 60)
        for module in sorted(module_failures.keys(), key=lambda m: module_failures[m]['total'], reverse=True):
            stats = module_failures[module]
            print(
                f'{module:20s} {stats["total"]:6d} {stats["llm"]:5d} {stats["applier"]:5d} {stats["compiler"]:5d} {stats["lec_mismatch"]:5d}'
            )
        print()

    # Detailed bug-by-bug breakdown
    print('=' * 80)
    if not latest_only:
        print('📋 DETAILED BUG-BY-BUG BREAKDOWN (All Runs, Grouped by Test Case):')
    else:
        print('📋 DETAILED BUG-BY-BUG BREAKDOWN:')
    print('=' * 80)

    # Group by test case to show multiple runs together
    test_case_groups = defaultdict(list)

    for analysis in all_analyses:
        # Create a unique key for each test case (bug) using bug_number from filename
        key = (analysis['bug_number'], analysis['verilog_file'], analysis['module_name'])
        test_case_groups[key].append(analysis)

    # Sort groups by bug number
    sorted_groups = sorted(test_case_groups.items(), key=lambda x: x[0][0])

    if show_timestamps:
        from datetime import datetime

        print(
            f'{"Bug":4s} {"Module":20s} {"File":25s} {"Timestamp":19s} {"LLM":5s} {"Apply":6s} {"Comp":5s} {"LEC":5s} {"Status":15s}'
        )
        print('-' * 120)
    else:
        print(f'{"Bug":4s} {"Module":20s} {"File":30s} {"LLM":5s} {"Apply":6s} {"Comp":5s} {"LEC":5s} {"Status":15s}')
        print('-' * 100)

    for (bug_number, verilog_file, module_name), analyses_list in sorted_groups:
        # Sort runs by timestamp (newest first)
        sorted_runs = sorted(analyses_list, key=lambda x: x.get('file_timestamp', 0), reverse=True)

        for i, a in enumerate(sorted_runs):
            # Use bug_number extracted from filename instead of bug_index
            bug_id = f'#{a["bug_number"]:02d}' if a['bug_number'] >= 0 else f'#{a["bug_index"] + 1:02d}'
            module = a['module_name'][:20]

            # Add indicator for multiple runs
            if len(sorted_runs) > 1 and not latest_only:
                if i == 0:
                    bug_id = f'{bug_id}🆕'  # Newest run
                else:
                    bug_id = f'{bug_id}📅'  # Older run

            if show_timestamps:
                from datetime import datetime

                source = a['source_file'][:25]
                timestamp_str = (
                    datetime.fromtimestamp(a['file_timestamp']).strftime('%Y-%m-%d %H:%M:%S')
                    if a.get('file_timestamp')
                    else 'N/A'
                )
                llm = '✅' if a['llm_success'] else '❌'
                applier = '✅' if a['applier_success'] else '❌'
                compiler = '✅' if a['compile_success'] else '❌'
                lec = '✅' if a['lec_equivalent'] else ('🔄' if a['lec_success'] else '❌')
                status = 'SUCCESS' if a['pipeline_success'] else (a['failure_reason'] or 'FAILED')
                print(
                    f'{bug_id:6s} {module:20s} {source:25s} {timestamp_str:19s} {llm:5s} {applier:6s} {compiler:5s} {lec:5s} {status:15s}'
                )
            else:
                source = a['source_file'][:30]
                llm = '✅' if a['llm_success'] else '❌'
                applier = '✅' if a['applier_success'] else '❌'
                compiler = '✅' if a['compile_success'] else '❌'
                lec = '✅' if a['lec_equivalent'] else ('🔄' if a['lec_success'] else '❌')
                status = 'SUCCESS' if a['pipeline_success'] else (a['failure_reason'] or 'FAILED')
                print(f'{bug_id:6s} {module:20s} {source:30s} {llm:5s} {applier:6s} {compiler:5s} {lec:5s} {status:15s}')

    print('=' * 80)

    # Show legend if there are multiple runs
    if not latest_only and any(len(runs) > 1 for _, runs in test_case_groups.items()):
        print('\n📅 Multiple runs detected:')
        print('   🆕 = Most recent run')
        print('   📅 = Previous run(s)')
        print()

    # Files that failed at each stage
    print()
    print('📁 FILES THAT FAILED AT EACH STAGE:')
    print('-' * 80)

    # LLM failures
    llm_failures = [a for a in all_analyses if not a['llm_success'] and a['has_hints']]
    if llm_failures:
        unique_modules = sorted(set(a['module_name'] for a in llm_failures))
        print(f'\n❌ LLM Generation Failed ({len(llm_failures)} bugs):')
        print(f'   Unique modules: {", ".join(unique_modules)}')
        # Show count per module
        module_counts = {}
        for a in llm_failures:
            module_counts[a['module_name']] = module_counts.get(a['module_name'], 0) + 1
        for module, count in sorted(module_counts.items(), key=lambda x: x[1], reverse=True):
            print(f'   - {module}: {count} failures')

    # Applier failures
    applier_failures = [a for a in all_analyses if a['llm_success'] and not a['applier_success']]
    if applier_failures:
        unique_modules = sorted(set(a['module_name'] for a in applier_failures))
        print(f'\n❌ Applier Failed ({len(applier_failures)} bugs):')
        print(f'   Unique modules: {", ".join(unique_modules)}')
        module_counts = {}
        for a in applier_failures:
            module_counts[a['module_name']] = module_counts.get(a['module_name'], 0) + 1
        for module, count in sorted(module_counts.items(), key=lambda x: x[1], reverse=True):
            print(f'   - {module}: {count} failures')

    # Compiler failures
    compiler_failures = [a for a in all_analyses if a['applier_success'] and not a['compile_success']]
    if compiler_failures:
        unique_modules = sorted(set(a['module_name'] for a in compiler_failures))
        print(f'\n❌ Compiler Failed ({len(compiler_failures)} bugs):')
        print(f'   Unique modules: {", ".join(unique_modules)}')
        module_counts = {}
        for a in compiler_failures:
            module_counts[a['module_name']] = module_counts.get(a['module_name'], 0) + 1
        for module, count in sorted(module_counts.items(), key=lambda x: x[1], reverse=True):
            print(f'   - {module}: {count} failures')

    # LEC mismatches (compiled but not equivalent)
    lec_mismatch_bugs = [a for a in all_analyses if a['lec_success'] and not a['lec_equivalent']]
    if lec_mismatch_bugs:
        unique_modules = sorted(set(a['module_name'] for a in lec_mismatch_bugs))
        print(f'\n⚠️  LEC Mismatch - Not Equivalent ({len(lec_mismatch_bugs)} bugs):')
        print(f'   Unique modules: {", ".join(unique_modules)}')
        module_counts = {}
        for a in lec_mismatch_bugs:
            module_counts[a['module_name']] = module_counts.get(a['module_name'], 0) + 1
        for module, count in sorted(module_counts.items(), key=lambda x: x[1], reverse=True):
            print(f'   - {module}: {count} failures')

    # Successful bugs
    successful_bugs_list = [a for a in all_analyses if a['lec_equivalent']]
    if successful_bugs_list:
        unique_modules = sorted(set(a['module_name'] for a in successful_bugs_list))
        print(f'\n✅ Successful - LEC Pass ({len(successful_bugs_list)} bugs):')
        print(f'   Unique modules: {", ".join(unique_modules)}')
        module_counts = {}
        for a in successful_bugs_list:
            module_counts[a['module_name']] = module_counts.get(a['module_name'], 0) + 1
        for module, count in sorted(module_counts.items(), key=lambda x: x[1], reverse=True):
            print(f'   - {module}: {count} successes')

    print()
    print('=' * 80)

    # LEC Mismatch details
    lec_mismatches = [a for a in all_analyses if a['lec_success'] and not a['lec_equivalent']]
    if lec_mismatches:
        print()
        print(f'⚠️  LEC MISMATCH DETAILS ({len(lec_mismatches)} bugs):')
        print('-' * 80)
        for a in lec_mismatches:
            bug_id = f'#{a["bug_number"]:02d}' if a['bug_number'] >= 0 else f'#{a["bug_index"] + 1:02d}'
            print(f'  Bug {bug_id} ({a["module_name"]}) - File: {a["source_file"]}')
            print('    LEC ran successfully but designs are NOT equivalent')
            print(f'    Total iterations: {a["total_attempts"]}')
            if a['lec_error']:
                print(f'    LEC message: {a["lec_error"][:100]}...')
        print()

    # Compiler failure details
    compiler_failures = [a for a in all_analyses if a['failure_reason'] == 'compiler_failed']
    if compiler_failures:
        print(f'⚠️  COMPILER FAILURE DETAILS ({len(compiler_failures)} bugs):')
        print('-' * 80)
        for a in compiler_failures:
            bug_id = f'#{a["bug_number"]:02d}' if a['bug_number'] >= 0 else f'#{a["bug_index"] + 1:02d}'
            print(f'  Bug {bug_id} ({a["module_name"]}) - File: {a["source_file"]}')
            print(f'    Total iterations: {a["total_attempts"]}')
            if a['compile_error']:
                error_preview = a['compile_error'][:150].replace('\n', ' ')
                print(f'    Error: {error_preview}...')
        print()


def main():
    parser = argparse.ArgumentParser(
        description='Summarize v2chisel_batch results from output directory',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Analyze results in a directory
  uv run python summarize_results.py -o /home/farzaneh/hagent/dino/gpt-5-codex-singlecycle-A

  # Analyze with verbose output
  uv run python summarize_results.py -o ./output_dir --verbose
        """,
    )
    parser.add_argument('-o', '--output-dir', required=True, help='Output directory containing YAML result files')
    parser.add_argument('--verbose', action='store_true', help='Show verbose output')
    parser.add_argument('--show-timestamps', action='store_true', help='Show file modification timestamps in output')
    parser.add_argument(
        '--latest-only', action='store_true', help='Show only the most recent run for each test case (hide historical runs)'
    )
    parser.add_argument(
        '--since', type=str, help='Only include files modified after this date (format: YYYY-MM-DD or "today" or "2 days ago")'
    )

    args = parser.parse_args()

    # Parse --since argument if provided
    since_timestamp = None
    if args.since:
        from datetime import datetime, timedelta
        import re

        if args.since.lower() == 'today':
            since_datetime = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
            since_timestamp = since_datetime.timestamp()
        elif match := re.match(r'(\d+)\s*(day|hour|minute)s?\s*ago', args.since.lower()):
            amount = int(match.group(1))
            unit = match.group(2)
            if unit == 'day':
                since_datetime = datetime.now() - timedelta(days=amount)
            elif unit == 'hour':
                since_datetime = datetime.now() - timedelta(hours=amount)
            elif unit == 'minute':
                since_datetime = datetime.now() - timedelta(minutes=amount)
            since_timestamp = since_datetime.timestamp()
        else:
            # Try to parse as YYYY-MM-DD
            try:
                since_datetime = datetime.strptime(args.since, '%Y-%m-%d')
                since_timestamp = since_datetime.timestamp()
            except ValueError:
                print(f'❌ Error: Invalid --since format: {args.since}')
                print('   Use YYYY-MM-DD, "today", or "N days/hours ago"')
                return 1

    output_dir = Path(args.output_dir)
    if not output_dir.exists():
        print(f'❌ Error: Directory does not exist: {output_dir}')
        return 1

    if not output_dir.is_dir():
        print(f'❌ Error: Not a directory: {output_dir}')
        return 1

    print(f'🔍 Scanning directory: {output_dir}')
    print()

    # Find all YAML files
    yaml_files = find_yaml_files(output_dir)

    # Filter by timestamp if --since specified
    if since_timestamp:
        from datetime import datetime

        filtered_files = [f for f in yaml_files if f.stat().st_mtime >= since_timestamp]
        print(f'🕒 Filtering files since {datetime.fromtimestamp(since_timestamp).strftime("%Y-%m-%d %H:%M:%S")}')
        print(f'   Before filter: {len(yaml_files)} files')
        print(f'   After filter: {len(filtered_files)} files')
        print()
        yaml_files = filtered_files

    if not yaml_files:
        print('⚠️  No YAML files found in directory')

        # Check individual_results directories
        individual_dirs = find_individual_results_dirs(output_dir)
        if individual_dirs:
            print(f'\n📁 Found {len(individual_dirs)} individual_results_* directories:')
            for d in individual_dirs:
                print(f'   - {d.name}')
            print('\n💡 Tip: Use the YAML files in the main directory, not individual_results/')

        return 1

    print(f'📄 Found {len(yaml_files)} YAML files')
    if args.verbose:
        from datetime import datetime

        for f in yaml_files:
            timestamp_str = datetime.fromtimestamp(f.stat().st_mtime).strftime('%Y-%m-%d %H:%M:%S')
            print(f'   - {f.name} (modified: {timestamp_str})')
    print()

    # Load and analyze all bug results
    all_analyses = []

    for yaml_file in yaml_files:
        if args.verbose:
            print(f'Loading {yaml_file.name}...')

        data = load_yaml_file(yaml_file)
        if not data:
            continue

        # Get file modification timestamp
        file_timestamp = yaml_file.stat().st_mtime

        bug_results = extract_bug_results(data)

        for bug_result in bug_results:
            analysis = analyze_single_bug(bug_result, source_file=yaml_file.name, file_timestamp=file_timestamp)
            all_analyses.append(analysis)

    if not all_analyses:
        print('❌ No bug results found in YAML files!')
        return 1

    print(f'✅ Analyzed {len(all_analyses)} bug results\n')

    # Print comprehensive summary
    print_summary(all_analyses, show_timestamps=args.show_timestamps, latest_only=args.latest_only)

    return 0


if __name__ == '__main__':
    exit(main())
