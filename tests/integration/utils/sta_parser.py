"""
STA Parser for Integration Tests

Provides utilities for parsing and validating Static Timing Analysis (STA) logs.
"""

import re
from pathlib import Path
from typing import Dict


def parse_sta_log(sta_log_path: Path) -> Dict[str, any]:
    """
    Extract timing metrics from sta.log file.

    Args:
        sta_log_path: Path to sta.log file

    Returns:
        Dict with timing metrics:
        - slack: List of slack values found
        - delay: List of delay values found
        - power: Dict with power metrics if present
        - has_timing_report: bool
        - has_power_report: bool
    """
    sta_log_path = Path(sta_log_path)

    if not sta_log_path.exists():
        raise FileNotFoundError(f'sta.log not found: {sta_log_path}')

    with open(sta_log_path) as f:
        content = f.read()

    results = {
        'slack': [],
        'delay': [],
        'power': {},
        'has_timing_report': False,
        'has_power_report': False,
        'raw_content': content,
    }

    # Parse timing report
    if 'report_checks' in content or 'Timing' in content:
        results['has_timing_report'] = True

        # Extract slack values (pattern: "slack" followed by number)
        slack_matches = re.findall(r'slack\s+(-?[\d.]+)', content, re.IGNORECASE)
        results['slack'] = [float(s) for s in slack_matches]

        # Extract delay values
        delay_matches = re.findall(r'delay\s+(-?[\d.]+)', content, re.IGNORECASE)
        results['delay'] = [float(d) for d in delay_matches]

    # Parse power report
    if 'report_power' in content or 'Power' in content:
        results['has_power_report'] = True

        # Extract total power
        power_match = re.search(r'Total\s+Power:\s+([\d.]+)', content, re.IGNORECASE)
        if power_match:
            results['power']['total'] = float(power_match.group(1))

        # Extract leakage power
        leakage_match = re.search(r'Leakage\s+Power:\s+([\d.]+)', content, re.IGNORECASE)
        if leakage_match:
            results['power']['leakage'] = float(leakage_match.group(1))

    return results


def validate_sta_results(sta_results: Dict[str, any], expected_ranges: Dict[str, Dict[str, float]]) -> bool:
    """
    Validate that STA results are within expected ranges.

    Args:
        sta_results: Results from parse_sta_log()
        expected_ranges: Dict with expected ranges for timing and power
                        Example: {
                            "timing": {"min_slack": -100, "max_slack": 1000, ...},
                            "power": {"min_total_power": 0, "max_total_power": 1, ...}
                        }

    Returns:
        True if all values are within expected ranges

    Raises:
        ValueError: If validation fails with details
    """
    errors = []

    # Validate timing
    if 'timing' in expected_ranges and sta_results['has_timing_report']:
        timing_ranges = expected_ranges['timing']

        # Check slack values
        if sta_results['slack']:
            for slack in sta_results['slack']:
                if not (timing_ranges.get('min_slack', float('-inf')) <= slack <= timing_ranges.get('max_slack', float('inf'))):
                    errors.append(
                        f'Slack {slack} outside expected range '
                        f'[{timing_ranges.get("min_slack")}, {timing_ranges.get("max_slack")}]'
                    )

        # Check delay values
        if sta_results['delay']:
            for delay in sta_results['delay']:
                if not (timing_ranges.get('min_delay', float('-inf')) <= delay <= timing_ranges.get('max_delay', float('inf'))):
                    errors.append(
                        f'Delay {delay} outside expected range '
                        f'[{timing_ranges.get("min_delay")}, {timing_ranges.get("max_delay")}]'
                    )

    # Validate power
    if 'power' in expected_ranges and sta_results['has_power_report']:
        power_ranges = expected_ranges['power']

        if 'total' in sta_results['power']:
            total_power = sta_results['power']['total']
            if not (power_ranges.get('min_total_power', 0) <= total_power <= power_ranges.get('max_total_power', float('inf'))):
                errors.append(
                    f'Total power {total_power} outside expected range '
                    f'[{power_ranges.get("min_total_power")}, {power_ranges.get("max_total_power")}]'
                )

        if 'leakage' in sta_results['power']:
            leakage = sta_results['power']['leakage']
            if not (power_ranges.get('min_leakage', 0) <= leakage <= power_ranges.get('max_leakage', float('inf'))):
                errors.append(
                    f'Leakage power {leakage} outside expected range '
                    f'[{power_ranges.get("min_leakage")}, {power_ranges.get("max_leakage")}]'
                )

    if errors:
        raise ValueError('STA validation failed:\\n' + '\\n'.join(errors))

    return True
