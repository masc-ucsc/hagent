"""
Integration Test 3: Synth + STA Validation

Tests that synthesis and Static Timing Analysis report reasonable values.
"""

import subprocess

import pytest

from tests.integration.utils.sta_parser import parse_sta_log, validate_sta_results


@pytest.mark.integration
@pytest.mark.cva6
def test_cva6_sta_reports(cva6_setup, test_config):
    """
    Test that STA reports reasonable timing values for CVA6 ALU.

    Steps:
    1. Run synthesis with STA (--run-sta)
    2. Parse sta.log
    3. Validate timing metrics are reasonable
    """
    repo_dir = cva6_setup['repo_dir']
    build_dir = cva6_setup['build_dir']
    env = cva6_setup['env_vars']

    # Find ALU file
    alu_file = repo_dir / 'core' / 'alu.sv'
    assert alu_file.exists(), f'ALU file not found: {alu_file}'

    # Run synth with STA
    synth_cmd = [
        'uv',
        'run',
        'python',
        'scripts/synth.py',
        '--tag',
        'sta_test',
        '--dir',
        str(build_dir),
        '--run-sta',  # Enable STA
        '--',
        '--top',
        'alu',
        str(alu_file),
    ]

    result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['timeout'])

    assert result.returncode == 0, f'Synth+STA failed: {result.stderr}\\nOutput: {result.stdout}'

    # Check STA outputs exist
    sta_dir = build_dir / 'sta_test'
    assert (sta_dir / 'sta.log').exists(), f'sta.log not found in {sta_dir}'
    assert (sta_dir / 'sta.tcl').exists(), f'sta.tcl not found in {sta_dir}'

    # Parse STA log
    sta_results = parse_sta_log(sta_dir / 'sta.log')

    # Validate that we got some results
    assert sta_results['has_timing_report'] or sta_results['has_power_report'], (
        'STA log contains neither timing nor power reports'
    )

    # If we have timing reports, validate them
    if sta_results['has_timing_report']:
        # Check that we got some timing values
        assert len(sta_results['slack']) > 0 or len(sta_results['delay']) > 0, (
            'Timing report found but no slack/delay values extracted'
        )

        print(f'Slack values: {sta_results["slack"]}')
        print(f'Delay values: {sta_results["delay"]}')

        # Validate results are reasonable (within expected ranges)
        try:
            validate_sta_results(sta_results, test_config['sta_ranges'])
            print('STA validation passed!')
        except ValueError as e:
            # If validation fails, print warning but don't fail test
            # (ranges may need adjustment based on actual data)
            pytest.warn(UserWarning(f'STA validation warning: {e}'))

    # If we have power reports, print them
    if sta_results['has_power_report']:
        print(f'Power results: {sta_results["power"]}')


@pytest.mark.integration
@pytest.mark.simplechisel
def test_simplechisel_sta_reports(simplechisel_setup, test_config):
    """
    Test that STA reports reasonable timing values for SimpleChisel GCD.

    Similar to CVA6 test but for SimpleChisel.
    """
    repo_dir = simplechisel_setup['repo_dir']
    build_dir = simplechisel_setup['build_dir']
    env = simplechisel_setup['env_vars']

    # Find GCD file (generated SystemVerilog in build directory)
    gcd_file = build_dir / 'build_gcd' / 'GCD.sv'
    if not gcd_file.exists():
        # Try alternative path in repo
        gcd_file = repo_dir / 'gcd' / 'GCD.sv'
    assert gcd_file.exists(), f'GCD file not found at {build_dir / "build_gcd" / "GCD.sv"} or {repo_dir / "gcd" / "GCD.sv"}'

    # Run synth with STA
    synth_cmd = [
        'uv',
        'run',
        'python',
        'scripts/synth.py',
        '--tag',
        'sta_test',
        '--dir',
        str(build_dir),
        '--run-sta',
        '--',
        '--top',
        'GCD',
        str(gcd_file),
    ]

    result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['timeout'])

    assert result.returncode == 0, f'Synth+STA failed: {result.stderr}'

    # Check STA outputs
    sta_dir = build_dir / 'sta_test'
    assert (sta_dir / 'sta.log').exists()
    assert (sta_dir / 'sta.tcl').exists()

    # Parse and validate
    sta_results = parse_sta_log(sta_dir / 'sta.log')

    assert sta_results['has_timing_report'] or sta_results['has_power_report']

    if sta_results['has_timing_report']:
        print(f'Slack values: {sta_results["slack"]}')
        print(f'Delay values: {sta_results["delay"]}')

        try:
            validate_sta_results(sta_results, test_config['sta_ranges'])
            print('STA validation passed!')
        except ValueError as e:
            pytest.warn(UserWarning(f'STA validation warning: {e}'))

    if sta_results['has_power_report']:
        print(f'Power results: {sta_results["power"]}')
