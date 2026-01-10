"""
Integration Test 1: Synth + LEC with Bug Injection

Tests the complete synthesis and logic equivalence checking workflow with
bug introduction and detection.
"""

import subprocess

import pytest

from tests.integration.utils.bug_injector import inject_bug, undo_bug


@pytest.mark.integration
@pytest.mark.cva6
@pytest.mark.slow
def test_cva6_alu_bug_detection(cva6_setup, test_config):
    """
    Test synth + LEC workflow with bug injection for CVA6 ALU.

    Steps:
    1. Synthesize reference (tag: "reference")
    2. Inject bug in ALU source
    3. Synthesize buggy (tag: "bug1") → LEC should FAIL
    4. Undo bug
    5. Synthesize fixed (tag: "nobug") → LEC should PASS
    """
    repo_dir = cva6_setup['repo_dir']
    build_dir = cva6_setup['build_dir']
    env = cva6_setup['env_vars']

    # Find ALU file
    alu_file = repo_dir / 'core' / 'alu.sv'
    assert alu_file.exists(), f'ALU file not found: {alu_file}'

    # ========================================================================
    # Phase 1: Synthesize reference
    # ========================================================================
    # Debug: Check HAGENT_DOCKER is set
    print(f'HAGENT_DOCKER={env.get("HAGENT_DOCKER", "NOT SET")}')
    print(f'HAGENT_REPO_DIR={env.get("HAGENT_REPO_DIR", "NOT SET")}')

    synth_cmd = [
        'uv',
        'run',
        'python',
        'scripts/synth.py',
        '--tag',
        'reference',
        '--dir',
        str(build_dir),
        '--',
        '--top',
        'alu',
        str(alu_file),
    ]

    result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['synth_timeout'])

    assert result.returncode == 0, f'Reference synth failed: {result.stderr}'

    ref_dir = build_dir / 'reference'
    assert (ref_dir / 'synth.v').exists(), 'Reference synth.v not created'
    assert (ref_dir / 'manifest.yaml').exists(), 'Reference manifest not created'

    # ========================================================================
    # Phase 2: Inject bug
    # ========================================================================
    # Simple bug: invert the result output
    bug_pattern = {'find': 'result_o = ', 'replace': 'result_o = ~'}
    original_content = inject_bug(alu_file, bug_pattern)

    try:
        # ====================================================================
        # Phase 3: Synthesize buggy version
        # ====================================================================
        synth_cmd[4] = 'bug1'  # Change tag to "bug1"

        result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['synth_timeout'])

        assert result.returncode == 0, f'Buggy synth failed: {result.stderr}'

        bug_dir = build_dir / 'bug1'
        assert (bug_dir / 'synth.v').exists(), 'Buggy synth.v not created'

        # ====================================================================
        # Phase 4: Run LEC - should FAIL
        # ====================================================================
        lec_cmd = [
            'uv',
            'run',
            'python',
            'hagent/tool/tests/cli_equiv_check.py',
            '--ref-tag',
            'reference',
            '--impl-tag',
            'bug1',
            '--dir',
            str(build_dir),
            '--use-synth',
        ]

        result = subprocess.run(lec_cmd, env=env, capture_output=True, text=True, timeout=test_config['lec_timeout'])

        # LEC should fail for buggy design
        assert result.returncode != 0, f'LEC should fail for buggy design, but passed. Output: {result.stdout}'

        # Check for failure indicators
        output = result.stdout + result.stderr
        assert 'FAILURE' in output or 'NOT equivalent' in output or 'not equivalent' in output, (
            f'Expected equivalence failure message in output: {output}'
        )

        # ====================================================================
        # Phase 5: Undo bug
        # ====================================================================
        undo_bug(alu_file, bug_pattern)

        # ====================================================================
        # Phase 6: Synthesize fixed version
        # ====================================================================
        synth_cmd[4] = 'nobug'  # Change tag to "nobug"

        result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['synth_timeout'])

        assert result.returncode == 0, f'Fixed synth failed: {result.stderr}'

        nobug_dir = build_dir / 'nobug'
        assert (nobug_dir / 'synth.v').exists(), 'Fixed synth.v not created'

        # ====================================================================
        # Phase 7: Run LEC - should PASS
        # ====================================================================
        lec_cmd[6] = 'nobug'  # Change impl-tag to "nobug"

        result = subprocess.run(lec_cmd, env=env, capture_output=True, text=True, timeout=test_config['lec_timeout'])

        assert result.returncode == 0, f'LEC should pass for fixed design: {result.stderr}\nOutput: {result.stdout}'

        # Check for success indicators
        output = result.stdout + result.stderr
        assert 'SUCCESS' in output or 'equivalent' in output.lower(), f'Expected equivalence success message in output: {output}'

    finally:
        # Restore original file content in case of test failure
        from tests.integration.utils.bug_injector import restore_file

        restore_file(alu_file, original_content)


@pytest.mark.integration
@pytest.mark.simplechisel
@pytest.mark.slow
def test_simplechisel_gcd_bug_detection(simplechisel_setup, test_config):
    """
    Test synth + LEC workflow with bug injection for SimpleChisel GCD.

    Similar to CVA6 test but for SimpleChisel GCD module.
    """
    repo_dir = simplechisel_setup['repo_dir']
    build_dir = simplechisel_setup['build_dir']
    env = simplechisel_setup['env_vars']

    # Find GCD file (generated SystemVerilog in build directory)
    # Debug: List what's actually in build_dir
    import os

    print(f'Build dir contents: {list(build_dir.iterdir()) if build_dir.exists() else "DIR DOES NOT EXIST"}')

    gcd_file = build_dir / 'build_gcd' / 'GCD.sv'
    if not gcd_file.exists():
        # Try alternative path in repo
        gcd_file = repo_dir / 'gcd' / 'GCD.sv'
    assert gcd_file.exists(), f'GCD file not found at {build_dir / "build_gcd" / "GCD.sv"} or {repo_dir / "gcd" / "GCD.sv"}'

    # Phase 1: Synthesize reference
    synth_cmd = [
        'uv',
        'run',
        'python',
        'scripts/synth.py',
        '--tag',
        'reference',
        '--dir',
        str(build_dir),
        '--',
        '--top',
        'GCD',
        str(gcd_file),
    ]

    result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['synth_timeout'])

    assert result.returncode == 0, f'Reference synth failed: {result.stderr}'

    ref_dir = build_dir / 'reference'
    assert (ref_dir / 'synth.v').exists()
    assert (ref_dir / 'manifest.yaml').exists()

    # Phase 2: Inject bug (flip comparison operator)
    bug_pattern = {'find': 'x > y', 'replace': 'x >= y'}
    original_content = inject_bug(gcd_file, bug_pattern)

    try:
        # Phase 3: Synthesize buggy version
        synth_cmd[4] = 'bug1'

        result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['synth_timeout'])

        assert result.returncode == 0, f'Buggy synth failed: {result.stderr}'

        # Phase 4: Run LEC - should FAIL
        lec_cmd = [
            'uv',
            'run',
            'python',
            'hagent/tool/tests/cli_equiv_check.py',
            '--ref-tag',
            'reference',
            '--impl-tag',
            'bug1',
            '--dir',
            str(build_dir),
            '--use-synth',
        ]

        result = subprocess.run(lec_cmd, env=env, capture_output=True, text=True, timeout=test_config['lec_timeout'])

        assert result.returncode != 0, 'LEC should fail for buggy design'

        # Phase 5: Undo bug
        undo_bug(gcd_file, bug_pattern)

        # Phase 6: Synthesize fixed version
        synth_cmd[4] = 'nobug'

        result = subprocess.run(synth_cmd, env=env, capture_output=True, text=True, timeout=test_config['synth_timeout'])

        assert result.returncode == 0, f'Fixed synth failed: {result.stderr}'

        # Phase 7: Run LEC - should PASS
        lec_cmd[6] = 'nobug'

        result = subprocess.run(lec_cmd, env=env, capture_output=True, text=True, timeout=test_config['lec_timeout'])

        assert result.returncode == 0, f'LEC should pass for fixed design: {result.stderr}'

    finally:
        # Restore original file
        from tests.integration.utils.bug_injector import restore_file

        restore_file(gcd_file, original_content)
