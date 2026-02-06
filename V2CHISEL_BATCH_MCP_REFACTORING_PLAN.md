# V2chisel_batch Refactoring Plan: Using MCP Profile System

**Goal**: Simplify v2chisel_batch by replacing hardcoded CPU type detection and SBT command construction with the existing MCP profile system from `hagent.yaml`.

**Benefits**:
- Remove ~330 lines of redundant code
- Better maintainability (add new CPU types in YAML, not Python)
- Consistent with rest of hagent ecosystem
- Better error messages (automatic file:line extraction)
- Testable independently with `mcp_build.py`

---

## Overview of Changes

### Files to Modify:
1. `hagent/step/v2chisel_batch/components/baseline_verilog_generator.py` (~150 lines → ~80 lines)
2. `hagent/step/v2chisel_batch/v2chisel_batch.py` (~200 lines affected)

### New Helper Functions to Add:
- `_get_profile_name(verilog_file, use_debug)` - Maps verilog filename to profile name
- `_get_build_dir_for_profile(profile_name)` - Maps profile name to build directory

### Methods to Remove:
- `_detect_cpu_type_from_verilog_file()` in baseline_verilog_generator.py
- `_detect_cpu_type_and_commands()` in v2chisel_batch.py

---

## Phase 1: Refactor baseline_verilog_generator.py

**Estimated impact**: 180 lines → 80 lines (100 lines removed)

### Change 1.1: Add New Helper Methods

**Location**: `hagent/step/v2chisel_batch/components/baseline_verilog_generator.py:34` (after `__init__`)

**Action**: Add these new methods

```python
def _get_profile_name(self, verilog_file: str, use_debug: bool = False) -> str:
    """
    Map verilog filename to hagent.yaml profile name.

    Args:
        verilog_file: Verilog filename (e.g., 'PipelinedCPU.sv')
        use_debug: If True, return debug profile; else no-debug profile

    Returns:
        Profile name from hagent.yaml (e.g., 'pipelined_nd')

    Examples:
        >>> _get_profile_name('SingleCycleCPU.sv', use_debug=False)
        'singlecyclecpu_nd'
        >>> _get_profile_name('PipelinedCPU.sv', use_debug=True)
        'pipelined_d'
        >>> _get_profile_name('PipelinedDualIssueCPU.sv', use_debug=False)
        'dualissue_nd'
    """
    verilog_lower = verilog_file.lower()

    # Determine base CPU type from filename
    if 'pipelined' in verilog_lower and 'dual' in verilog_lower:
        base = 'dualissue'
    elif 'pipelined' in verilog_lower:
        base = 'pipelined'
    else:
        base = 'singlecyclecpu'

    # Add debug suffix
    suffix = '_d' if use_debug else '_nd'
    return f'{base}{suffix}'

def _get_build_dir_for_profile(self, profile_name: str) -> str:
    """
    Get build directory name for a profile.

    Args:
        profile_name: Profile name from hagent.yaml (e.g., 'pipelined_nd')

    Returns:
        Build directory name (e.g., 'build_pipelined_nd')

    Examples:
        >>> _get_build_dir_for_profile('pipelined_nd')
        'build_pipelined_nd'
        >>> _get_build_dir_for_profile('singlecyclecpu_d')
        'build_singlecyclecpu_d'
    """
    # Static mapping - these directory names are defined in hagent.yaml
    BUILD_DIR_MAP = {
        'singlecyclecpu_nd': 'build_singlecyclecpu_nd',
        'singlecyclecpu_d': 'build_singlecyclecpu_d',
        'pipelined_nd': 'build_pipelined_nd',
        'pipelined_d': 'build_pipelined_d',
        'dualissue_nd': 'build_dualissue_nd',
        'dualissue_d': 'build_dualissue_d',
    }
    return BUILD_DIR_MAP.get(profile_name, 'build_singlecyclecpu_nd')
```

**Rationale**: These helper methods replace the ~100 lines of CPU type detection logic with a simple, clear mapping.

---

### Change 1.2: Remove Old Detection Method

**Location**: `baseline_verilog_generator.py:34-69`

**Action**: DELETE this entire method

```python
# DELETE THIS METHOD (lines 34-69):
def _detect_cpu_type_from_verilog_file(self, verilog_file: str) -> Dict[str, str]:
    """
    Detect CPU type from verilog filename and return appropriate commands.
    ...
    """
    # ... ~35 lines of hardcoded detection logic
```

**Rationale**: This method is replaced by `_get_profile_name()` which is much simpler.

---

### Change 1.3: Update generate_fresh_baseline Method

**Location**: `baseline_verilog_generator.py:106-127`

**BEFORE** (old code):
```python
# Lines 106-127 (OLD):
for cpu_type in cpu_types_needed:
    # Get a verilog file that matches this CPU type to get the right command
    sample_file = self._get_sample_verilog_file_for_cpu_type(cpu_type)
    cpu_info = self._detect_cpu_type_from_verilog_file(sample_file)

    sbt_command = cpu_info['sbt_command_nodebug']
    build_dir_nodebug = cpu_info['build_dir_nodebug']  # NoDebug command generates here

    exit_code, stdout, stderr = self.builder.run_cmd(
        f'bash -l -c \'cd /code/workspace/repo && {sbt_command}\''
    )

    if exit_code == 0:
        # Files are already in the correct location (build_dir_nodebug)
        # Just verify they exist and catalog them
        copy_result = {'success': True}  # No copy needed

        if copy_result['success']:
            # Find and catalog the generated files
            verilog_files = self._find_baseline_verilog_files_for_cpu_type(build_dir_nodebug)
            all_files.update(verilog_files)
            all_commands_used.append(sbt_command)
```

**AFTER** (new code):
```python
# Lines 106-127 (NEW):
for cpu_type in cpu_types_needed:
    # Get a sample verilog file for this CPU type
    sample_file = self._get_sample_verilog_file_for_cpu_type(cpu_type)

    # Get profile name and build directory
    profile_name = self._get_profile_name(sample_file, use_debug=False)
    build_dir = self._get_build_dir_for_profile(profile_name)

    # Use Builder's run_api instead of manual command construction
    exit_code, stdout, stderr = self.builder.run_api(
        exact_name=profile_name,
        command_name='compile',
        quiet=True
    )

    if exit_code == 0:
        # Find and catalog the generated files
        verilog_files = self._find_baseline_verilog_files_for_cpu_type(build_dir)
        all_files.update(verilog_files)
        all_commands_used.append(f'profile={profile_name}, api=compile')
```

**Changes**:
- ✅ Remove `_detect_cpu_type_from_verilog_file()` call
- ✅ Replace with `_get_profile_name()` and `_get_build_dir_for_profile()`
- ✅ Replace `builder.run_cmd()` with `builder.run_api()`
- ✅ No more bash wrapper (`bash -l -c`)
- ✅ No more manual SBT command construction

**Benefits**:
- Cleaner code (18 lines → 14 lines)
- Builder handles Docker/local mode automatically
- Better error messages from mcp_build
- Consistent with MCP architecture

---

### Change 1.4: Update backup_baseline_verilog Method

**Location**: `baseline_verilog_generator.py:272-298`

**BEFORE** (old code):
```python
# Lines 287-293 (OLD):
elif verilog_file:
    # Detect from verilog filename
    cpu_info = self._detect_cpu_type_from_verilog_file(verilog_file)
    build_dir = cpu_info['build_dir_nodebug']
    if self.debug:
        print(f'🔍 [BASELINE] Using CPU-type-aware backup for {cpu_info["cpu_type"]}: {build_dir}')
    verilog_files = self._find_baseline_verilog_files_for_cpu_type(build_dir)
```

**AFTER** (new code):
```python
# Lines 287-293 (NEW):
elif verilog_file:
    # Get profile and build directory
    profile_name = self._get_profile_name(verilog_file, use_debug=False)
    build_dir = self._get_build_dir_for_profile(profile_name)
    if self.debug:
        print(f'🔍 [BASELINE] Using profile-based backup: {profile_name} -> {build_dir}')
    verilog_files = self._find_baseline_verilog_files_for_cpu_type(build_dir)
```

**Changes**:
- ✅ Replace `_detect_cpu_type_from_verilog_file()` with `_get_profile_name()` and `_get_build_dir_for_profile()`
- ✅ Update debug message to mention "profile" instead of "CPU type"

---

## Phase 2: Refactor v2chisel_batch.py

**Estimated impact**: ~150 lines modified, ~80 lines removed

### Change 2.1: Add New Helper Methods

**Location**: `hagent/step/v2chisel_batch/v2chisel_batch.py:1365` (before `_detect_cpu_type_and_commands`)

**Action**: Add these new methods (same as Phase 1)

```python
def _get_profile_name(self, verilog_file: str, use_debug: bool = False) -> str:
    """
    Map verilog filename to hagent.yaml profile name.

    Args:
        verilog_file: Verilog filename (e.g., 'PipelinedCPU.sv')
        use_debug: If True, return debug profile; else no-debug profile

    Returns:
        Profile name from hagent.yaml (e.g., 'pipelined_nd')
    """
    verilog_lower = verilog_file.lower()

    if 'pipelined' in verilog_lower and 'dual' in verilog_lower:
        base = 'dualissue'
    elif 'pipelined' in verilog_lower:
        base = 'pipelined'
    else:
        base = 'singlecyclecpu'

    suffix = '_d' if use_debug else '_nd'
    return f'{base}{suffix}'

def _get_build_dir_for_profile(self, profile_name: str) -> str:
    """Get build directory name for a profile."""
    BUILD_DIR_MAP = {
        'singlecyclecpu_nd': 'build_singlecyclecpu_nd',
        'singlecyclecpu_d': 'build_singlecyclecpu_d',
        'pipelined_nd': 'build_pipelined_nd',
        'pipelined_d': 'build_pipelined_d',
        'dualissue_nd': 'build_dualissue_nd',
        'dualissue_d': 'build_dualissue_d',
    }
    return BUILD_DIR_MAP.get(profile_name, 'build_singlecyclecpu_nd')
```

---

### Change 2.2: Remove Old Detection Method

**Location**: `v2chisel_batch.py:1365-1436`

**Action**: DELETE this entire method

```python
# DELETE THIS METHOD (lines 1365-1436):
def _detect_cpu_type_and_commands(self, verilog_file: str) -> Dict[str, str]:
    """
    Detect CPU type from verilog filename and return commands/paths.
    ...
    """
    # ... ~70 lines of hardcoded detection logic
```

**Rationale**: Replaced by `_get_profile_name()`.

---

### Change 2.3: Update _generate_verilog_with_applied_fix Method

**Location**: `v2chisel_batch.py:1437-1520`

**BEFORE** (old code - lines ~1445-1465):
```python
# OLD:
# Detect CPU type - prefer pre-detected types for filtered bugs
if hasattr(self, '_detected_cpu_types') and self._detected_cpu_types:
    cpu_type = self._detected_cpu_types[0]
    if cpu_type == 'pipelined_dual':
        sample_file = 'PipelinedDualIssueCPU.sv'
    elif cpu_type == 'pipelined_single':
        sample_file = 'PipelinedCPU.sv'
    else:
        sample_file = 'SingleCycleCPU.sv'
    cpu_info = self._detect_cpu_type_and_commands(sample_file)
    print(f'🎯 [VERILOG_GEN] Using pre-detected CPU type: {cpu_type}')
elif verilog_file:
    cpu_info = self._detect_cpu_type_and_commands(verilog_file)
    print(f'🎯 [VERILOG_GEN] Detected CPU type from filename: {cpu_info["cpu_type"]}')
else:
    cpu_info = self._detect_cpu_type_and_commands('SingleCycleCPU.sv')

# Get SBT command
sbt_command = cpu_info['sbt_command_debug']

# Execute SBT command
exit_code, stdout, stderr = self.builder.run_cmd(
    f'bash -l -c \'cd /code/workspace/repo && {sbt_command}\''
)
```

**AFTER** (new code):
```python
# NEW:
# Determine verilog file for profile detection
if hasattr(self, '_detected_cpu_types') and self._detected_cpu_types:
    cpu_type = self._detected_cpu_types[0]
    if cpu_type == 'pipelined_dual':
        sample_file = 'PipelinedDualIssueCPU.sv'
    elif cpu_type == 'pipelined_single':
        sample_file = 'PipelinedCPU.sv'
    else:
        sample_file = 'SingleCycleCPU.sv'
    print(f'🎯 [VERILOG_GEN] Using pre-detected CPU type: {cpu_type}')
elif verilog_file:
    sample_file = verilog_file
    print(f'🎯 [VERILOG_GEN] Using verilog file: {verilog_file}')
else:
    sample_file = 'SingleCycleCPU.sv'

# Get profile name and use Builder's run_api
profile_name = self._get_profile_name(sample_file, use_debug=True)

# Execute compilation via Builder API
exit_code, stdout, stderr = self.builder.run_api(
    exact_name=profile_name,
    command_name='compile',
    quiet=True
)
```

**Changes**:
- ✅ Remove all `_detect_cpu_type_and_commands()` calls
- ✅ Replace with `_get_profile_name()`
- ✅ Use `builder.run_api()` instead of `run_cmd()` with bash wrapper
- ✅ Use debug profile (`use_debug=True`) for verilog generation

---

### Change 2.4: Update _run_lec Method - Build Directory Detection

**Location**: `v2chisel_batch.py:1916-1943`

**BEFORE** (old code):
```python
# Lines 1916-1943 (OLD):
# Use pre-detected CPU types if available
if hasattr(self, '_detected_cpu_types') and self._detected_cpu_types:
    cpu_type = self._detected_cpu_types[0]
    if cpu_type == 'pipelined_dual':
        sample_file = 'PipelinedDualIssueCPU.sv'
    elif cpu_type == 'pipelined_single':
        sample_file = 'PipelinedCPU.sv'
    else:
        sample_file = 'SingleCycleCPU.sv'
    cpu_info = self._detect_cpu_type_and_commands(sample_file)
    print(f'🔍 [LEC] Using pre-detected CPU type: {cpu_type}')
else:
    cpu_info = self._detect_cpu_type_and_commands(target_file)
    print(f'🔍 [LEC] Detected CPU type from filename')

gate_build_dir = cpu_info['build_dir_debug']
```

**AFTER** (new code):
```python
# Lines 1916-1943 (NEW):
# Determine verilog file for profile detection
if hasattr(self, '_detected_cpu_types') and self._detected_cpu_types:
    cpu_type = self._detected_cpu_types[0]
    if cpu_type == 'pipelined_dual':
        sample_file = 'PipelinedDualIssueCPU.sv'
    elif cpu_type == 'pipelined_single':
        sample_file = 'PipelinedCPU.sv'
    else:
        sample_file = 'SingleCycleCPU.sv'
    print(f'🔍 [LEC] Using pre-detected CPU type: {cpu_type}')
else:
    sample_file = target_file
    print(f'🔍 [LEC] Using target file: {target_file}')

# Get profile name and build directory
profile_name = self._get_profile_name(sample_file, use_debug=True)
gate_build_dir = self._get_build_dir_for_profile(profile_name)
```

**Changes**:
- ✅ Remove `_detect_cpu_type_and_commands()` call
- ✅ Replace with `_get_profile_name()` and `_get_build_dir_for_profile()`
- ✅ Use debug profile for LEC (matches verilog generation)

---

### Change 2.5: Update All Hardcoded Build Directory References

**Locations**: Search for all occurrences of `'build_singlecyclecpu'` and replace with profile-based lookup.

**Files to check**:
- Backup/restore operations
- Golden design creation
- Any file path construction

**Pattern to find**:
```bash
grep -n "build_singlecyclecpu\|build_pipelined\|build_dualissue" v2chisel_batch.py
```

**Replacement strategy**:
1. Identify the verilog_file variable in context
2. Add: `profile_name = self._get_profile_name(verilog_file, use_debug=appropriate_value)`
3. Add: `build_dir = self._get_build_dir_for_profile(profile_name)`
4. Replace hardcoded string with `build_dir` variable

---

## Testing Strategy

### Phase 1 Testing: baseline_verilog_generator.py

**Test 1.1: Unit test for new helper methods**
```python
# Create test file: hagent/step/v2chisel_batch/tests/test_profile_helpers.py
def test_get_profile_name():
    generator = BaselineVerilogGenerator(mock_builder)

    # Test single-cycle
    assert generator._get_profile_name('SingleCycleCPU.sv', False) == 'singlecyclecpu_nd'
    assert generator._get_profile_name('SingleCycleCPU.sv', True) == 'singlecyclecpu_d'

    # Test pipelined
    assert generator._get_profile_name('PipelinedCPU.sv', False) == 'pipelined_nd'
    assert generator._get_profile_name('PipelinedCPU.sv', True) == 'pipelined_d'

    # Test dual issue
    assert generator._get_profile_name('PipelinedDualIssueCPU.sv', False) == 'dualissue_nd'

def test_get_build_dir_for_profile():
    generator = BaselineVerilogGenerator(mock_builder)

    assert generator._get_build_dir_for_profile('pipelined_nd') == 'build_pipelined_nd'
    assert generator._get_build_dir_for_profile('singlecyclecpu_d') == 'build_singlecyclecpu_d'
```

**Test 1.2: Integration test with actual Builder**
```bash
# Set up environment
export HAGENT_DOCKER="mascucsc/hagent-simplechisel:2026.02"
export HAGENT_REPO_DIR="/tmp/test_v2chisel/repo"
export HAGENT_BUILD_DIR="/tmp/test_v2chisel/build"
export HAGENT_CACHE_DIR="/tmp/test_v2chisel/cache"

# Run baseline generation for single bug
uv run python hagent/step/v2chisel_batch/v2chisel_batch.py \
  -o /tmp/test_output \
  --bugs 01 \
  dino/inputs/gpt-5-codex/all_verilog_diffs_A_pipelinesingle.yaml

# Verify:
# 1. No errors in output
# 2. Baseline generation succeeded
# 3. Files created in correct build directory
```

**Test 1.3: Compare output with old implementation**
```bash
# Before refactoring, save output
git stash  # Stash refactored changes
uv run python ... > /tmp/old_output.txt
git stash pop

# After refactoring
uv run python ... > /tmp/new_output.txt

# Compare (should be identical except for debug messages)
diff /tmp/old_output.txt /tmp/new_output.txt
```

---

### Phase 2 Testing: v2chisel_batch.py

**Test 2.1: Single-cycle CPU**
```bash
uv run python hagent/step/v2chisel_batch/v2chisel_batch.py \
  -o /tmp/test_singlecycle \
  --bugs 01 \
  dino/inputs/gpt-5-codex/all_verilog_diffs_A_singlecycle.yaml
```

**Test 2.2: Pipelined single-issue CPU**
```bash
uv run python hagent/step/v2chisel_batch/v2chisel_batch.py \
  -o /tmp/test_pipelined \
  --bugs 01 \
  dino/inputs/gpt-5-codex/all_verilog_diffs_A_pipelinesingle.yaml
```

**Test 2.3: Pipelined dual-issue CPU** (if available)
```bash
uv run python hagent/step/v2chisel_batch/v2chisel_batch.py \
  -o /tmp/test_dualissue \
  --bugs 01 \
  dino/inputs/gpt-5-codex/all_verilog_diffs_A_pipelinedual.yaml
```

**Test 2.4: Full existing test suite**
```bash
uv run pytest hagent/step/v2chisel_batch/tests/ -v
```

---

## Rollback Plan

If any issues occur during refactoring:

**Option 1: Git revert**
```bash
git stash  # Save current changes
git log --oneline -5  # Find commit before refactoring
git revert <commit-hash>
```

**Option 2: Keep old methods temporarily**
```python
# Rename old methods instead of deleting
def _detect_cpu_type_and_commands_OLD(self, verilog_file: str):
    # Keep old implementation
    ...

# Add fallback in new code
try:
    profile_name = self._get_profile_name(verilog_file)
    # ... new code ...
except Exception as e:
    print(f"⚠️ Profile system failed, falling back to old method: {e}")
    cpu_info = self._detect_cpu_type_and_commands_OLD(verilog_file)
    # ... old code path ...
```

---

## Validation Checklist

Before considering refactoring complete:

### Code Quality
- [ ] All ruff checks pass: `uv run ruff check hagent`
- [ ] All ruff format pass: `uv run ruff format hagent`
- [ ] No new TODO/FIXME comments added
- [ ] All debug print statements use consistent format

### Testing
- [ ] All existing tests pass: `uv run pytest hagent/step/v2chisel_batch/tests/ -v`
- [ ] New unit tests added for helper methods
- [ ] Integration test with single-cycle CPU passes
- [ ] Integration test with pipelined CPU passes
- [ ] Integration test with dual-issue CPU passes (if applicable)

### Documentation
- [ ] Docstrings added for new methods
- [ ] Examples added to docstrings
- [ ] README updated (if needed)
- [ ] Commit message includes "BREAKING CHANGE:" if API changed

### Verification
- [ ] Baseline generation works for all CPU types
- [ ] Verilog generation works for all CPU types
- [ ] LEC runs successfully for all CPU types
- [ ] Golden design creation works
- [ ] Backup/restore functionality preserved
- [ ] Error messages are clear and helpful

---

## Implementation Timeline

**Phase 1: baseline_verilog_generator.py** (Estimated: 2-3 hours)
1. Create and test helper methods (30 min)
2. Update generate_fresh_baseline (45 min)
3. Update backup_baseline_verilog (30 min)
4. Remove old method (15 min)
5. Run tests and verify (45 min)

**Phase 2: v2chisel_batch.py** (Estimated: 3-4 hours)
1. Add helper methods (30 min)
2. Update verilog generation (60 min)
3. Update LEC method (45 min)
4. Replace hardcoded paths (60 min)
5. Remove old method (15 min)
6. Full testing (60 min)

**Total estimated time**: 5-7 hours

---

## Risk Assessment

### Low Risk Changes
- ✅ Adding new helper methods (no existing code affected)
- ✅ Updating debug print statements
- ✅ Renaming variables for clarity

### Medium Risk Changes
- ⚠️ Replacing `builder.run_cmd()` with `builder.run_api()`
  - **Mitigation**: Test with all CPU types, verify error handling
- ⚠️ Removing old detection methods
  - **Mitigation**: Keep methods commented out for first commit

### High Risk Changes
- ❗ Changing build directory paths
  - **Mitigation**: Extensive testing, verify backup/restore still works
- ❗ Modifying LEC gate file detection
  - **Mitigation**: Test LEC with all CPU types, verify equivalence checking

---

## Success Criteria

The refactoring is successful if:

1. ✅ **All tests pass**: No regressions in existing functionality
2. ✅ **Code reduction**: At least 250 lines removed
3. ✅ **Performance**: No significant slowdown (< 5% increase in runtime)
4. ✅ **Maintainability**: New CPU types can be added by editing only `hagent.yaml`
5. ✅ **Error messages**: Better error messages with file:line references
6. ✅ **Consistency**: Uses same profile system as rest of hagent

---

## Future Enhancements (Post-Refactoring)

After refactoring is complete and stable:

1. **Dynamic profile discovery**: Instead of hardcoded `BUILD_DIR_MAP`, query Builder for build directories
2. **Profile validation**: Add startup check to verify all required profiles exist in `hagent.yaml`
3. **Better error messages**: Use mcp_build's error detection in v2chisel_batch
4. **Profile caching**: Cache profile lookups to avoid repeated parsing
5. **Multi-project support**: Extend to support projects beyond simplechisel (cva6, soomrv, etc.)

---

## Questions for User

Before implementing:

1. **Testing environment**: Do you have a test environment set up with Docker?
2. **Input files**: Do you have test input files for all three CPU types (single-cycle, pipelined, dual-issue)?
3. **CI/CD**: Should I add the refactored code in a feature branch or directly to main?
4. **Timing**: When would you like me to start implementing? Should we do Phase 1 first and test before Phase 2?
5. **Backup**: Should I create a backup branch before starting?

---

## Appendix A: Profile System Reference

### Available Profiles in hagent.yaml

```yaml
singlecyclecpu_nd:
  command: sbt "runMain dinocpu.SingleCycleCPUNoDebug"
  output: build_singlecyclecpu_nd

singlecyclecpu_d:
  command: sbt "runMain dinocpu.SingleCycleCPUDebug"
  output: build_singlecyclecpu_d

pipelined_nd:
  command: sbt "runMain dinocpu.pipelined.PipelinedNoDebug"
  output: build_pipelined_nd

pipelined_d:
  command: sbt "runMain dinocpu.pipelined.PipelinedDebug"
  output: build_pipelined_d

dualissue_nd:
  command: sbt "runMain dinocpu.pipelined.PipelinedDualIssueNoDebug"
  output: build_dualissue_nd

dualissue_d:
  command: sbt "runMain dinocpu.pipelined.PipelinedDualIssueDebug"
  output: build_dualissue_d
```

### Builder API Usage

```python
# Old way (manual command):
exit_code, stdout, stderr = builder.run_cmd(
    'bash -l -c \'cd /code/workspace/repo && sbt "runMain dinocpu.pipelined.PipelinedDebug"\''
)

# New way (profile-based):
exit_code, stdout, stderr = builder.run_api(
    exact_name='pipelined_d',
    command_name='compile',
    quiet=True
)
```

### Testing Individual Profiles

```bash
# Set up environment
export HAGENT_DOCKER="mascucsc/hagent-simplechisel:2026.02"
export HAGENT_REPO_DIR="path/to/dinocpu"
export HAGENT_BUILD_DIR="path/to/build"
export HAGENT_CACHE_DIR="path/to/cache"

# Test single profile
uv run python hagent/mcp/mcp_build.py --name pipelined_nd --api compile

# List all available profiles
uv run python hagent/mcp/mcp_build.py --list
```

---

**End of Refactoring Plan**

This plan is ready for review. Please let me know:
1. If you approve this plan
2. If you want any changes/additions
3. When you'd like me to start implementing

Once approved, I will proceed with Phase 1 first, test it thoroughly, and only then move to Phase 2.
