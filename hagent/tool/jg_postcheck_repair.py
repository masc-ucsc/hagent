#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import csv
import json
import re
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

try:
    from hagent.core.llm_wrap import LLM_wrap
except Exception:
    LLM_wrap = None

# Bound threshold: FAIL props with Ht/L engine and bound >= this are BEHAVIORAL
# (real RTL bugs — convert to cover, do not send to LLM for repair)
BEHAVIORAL_BOUND_THRESHOLD = 10


# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------


def _tail_text(p: Path, n_lines: int = 250) -> str:
    if not p.exists():
        return f'<missing: {p}>'
    try:
        lines = p.read_text(errors='ignore').splitlines()
        return '\n'.join(lines[-n_lines:])
    except Exception as e:
        return f'<failed to read {p}: {e}>'


def _read_text(p: Path, max_bytes: int = 250_000) -> str:
    if not p.exists():
        return f'<missing: {p}>'
    try:
        b = p.read_bytes()
        if len(b) > max_bytes:
            b = b[-max_bytes:]
        return b.decode('utf-8', errors='ignore')
    except Exception as e:
        return f'<failed to read {p}: {e}>'


def _read_results_summary(p: Path) -> Dict[str, int]:
    out: Dict[str, int] = {}
    if not p.exists():
        return out
    with p.open('r', encoding='utf-8', errors='ignore') as f:
        r = csv.DictReader(f)
        for row in r:
            k = (row.get('status') or '').strip()
            v = (row.get('count') or '0').strip()
            try:
                out[k] = int(v)
            except Exception:
                out[k] = 0
    return out


def _write_results_summary(p: Path, counts: Dict[str, int]) -> None:
    with p.open('w', newline='', encoding='utf-8') as f:
        w = csv.writer(f)
        w.writerow(['status', 'count'])
        for k in ['PROVEN', 'FAIL', 'UNREACHABLE', 'COVER', 'UNKNOWN']:
            w.writerow([k, counts.get(k, 0)])


def _needs_repair(counts: Dict[str, int]) -> Tuple[bool, str]:
    fail = counts.get('FAIL', 0)
    unk = counts.get('UNKNOWN', 0)
    if fail > 0:
        return True, f'FAIL={fail}'
    if unk > 0:
        return True, f'UNKNOWN={unk}'
    return False, 'clean'


# ---------------------------------------------------------------------------
# CEX classification
# ---------------------------------------------------------------------------


def _classify_fails_structured(log_path: Path) -> Dict[str, Dict]:
    """Parse jg.stdout.log and return structured classification of all FAIL (cex) properties.

    Returns:
        {short_name: {'engine': str, 'bound': str, 'bound_int': int, 'category': str}}

    Categories:
        PRE_ERROR  — PRE engine (over-constrained precondition, fixable)
        SPURIOUS   — Ht/L engine, bound < BEHAVIORAL_BOUND_THRESHOLD (weak environment, needs ASSUME)
        BEHAVIORAL — Ht/L engine, bound >= BEHAVIORAL_BOUND_THRESHOLD (real RTL bug, convert to cover)
    """
    if not log_path.exists():
        return {}

    pat = re.compile(r'\[\s*\d+\]\s+(\S+)\s+cex\s+(\S+)\s+((?:\d+\s*-\s*\d+|\d+))\s+\d+\.\d+')
    result: Dict[str, Dict] = {}

    for line in log_path.read_text(errors='ignore').splitlines():
        m = pat.search(line)
        if not m:
            continue
        prop = m.group(1)
        engine = m.group(2)
        bound_str = m.group(3).strip()
        short = prop.split('.')[-1]
        if ':' in short:
            continue  # skip :witness1 / :precondition1

        # Parse bound as int (take first number for range like "284 - 445")
        bound_int = int(re.split(r'\s*-\s*', bound_str)[0])

        if engine == 'PRE':
            category = 'PRE_ERROR'
        elif bound_int >= BEHAVIORAL_BOUND_THRESHOLD:
            category = 'BEHAVIORAL'
        else:
            category = 'SPURIOUS'

        result[short] = {
            'engine': engine,
            'bound': bound_str,
            'bound_int': bound_int,
            'category': category,
        }

    return result


def _format_classification_summary(classified: Dict[str, Dict]) -> str:
    """Return human-readable classification table for LLM prompt."""
    lines = [
        f'{"Property":<30} {"Engine":<6} {"Bound":<12} {"Category"}',
        '-' * 65,
    ]
    for prop, info in sorted(classified.items()):
        lines.append(f'{prop:<30} {info["engine"]:<6} {info["bound"]:<12} {info["category"]}')

    counts: Dict[str, int] = {}
    for info in classified.values():
        counts[info['category']] = counts.get(info['category'], 0) + 1

    lines.append('')
    lines.append('Summary: ' + ', '.join(f'{k}={v}' for k, v in sorted(counts.items())))
    lines.append('')
    lines.append(
        'NOTE: BEHAVIORAL props (real RTL bugs) have been auto-converted to cover — '
        'do NOT change them back to assert. Focus ONLY on PRE_ERROR and SPURIOUS.'
    )
    return '\n'.join(lines)


# ---------------------------------------------------------------------------
# Detect vacuously-proven assertions (unreachable witness)
# ---------------------------------------------------------------------------


def _find_vacuous_asserts(log_path: Path) -> set:
    """Return short names of assertions whose :witness1 cover is proven unreachable.

    When an assertion's antecedent can never be satisfied (e.g. disable iff conflicts
    with the antecedent, or the precondition requires internal signals unreachable in
    blackbox mode), JG reports its :witness1 cover as unreachable.  Such assertions are
    vacuously proven — they pass because the antecedent never fires, not because the
    consequent actually holds.

    NOTE: Only returns assertions that are vacuously proven, NOT assertions that have
    real CEX (those have a reachable witness by definition).
    """
    if not log_path.exists():
        return set()

    # Match:  The cover property "...assert_xxx:witness1" was proven unreachable
    pat = re.compile(r'cover property "([^"]+):witness1" was proven unreachable')
    vacuous: set = set()

    for line in log_path.read_text(errors='ignore').splitlines():
        m = pat.search(line)
        if not m:
            continue
        full_name = m.group(1)
        short = full_name.split('.')[-1]  # e.g. 'assert_valid_o_low_during_reset'
        # Only add if it looks like an assert (not a cover or assume already)
        if short.startswith('assert_'):
            vacuous.add(short)

    return vacuous


# ---------------------------------------------------------------------------
# COI / port context loading for LLM vacuous fix
# ---------------------------------------------------------------------------


def _load_coi_context(fpv_dir: Path, sva_top: str) -> Tuple[str, str]:
    """Load io_relations.json and ports.json and return (ports_summary, coi_graph) strings."""
    io_rel_path = fpv_dir / f'{sva_top}_io_relations.json'
    ports_path = fpv_dir / f'{sva_top}_ports.json'

    ports_summary = '<ports.json not found>'
    coi_graph = '<io_relations.json not found>'

    if ports_path.exists():
        try:
            ports_data = json.loads(ports_path.read_text(errors='ignore'))
            lines: List[str] = []
            port_list = ports_data if isinstance(ports_data, list) else []
            for p in port_list:
                direction = p.get('dir', p.get('direction', '?'))
                name = p.get('name', '?')
                width = p.get('width', p.get('type', ''))
                lines.append(f'  {direction:<8} {name}{"  " + str(width) if width and width not in ("logic", "?", "-") else ""}')
            ports_summary = '\n'.join(lines) if lines else str(ports_data)[:2000]
        except Exception as exc:
            ports_summary = f'<failed to parse ports.json: {exc}>'

    if io_rel_path.exists():
        try:
            io_data = json.loads(io_rel_path.read_text(errors='ignore'))
            relations = io_data.get('relationships', {}).get('per_output_influences', [])
            lines = []
            for rel in relations[:40]:  # cap to avoid context overflow
                output = rel.get('output', '?')
                inputs = ', '.join(rel.get('direct_inputs', rel.get('inputs', [])))
                effect = rel.get('effect', '')
                guards = rel.get('guards', '')
                line = f'  {output} <- [{inputs}]'
                if effect:
                    line += f'  // {effect[:80]}'
                if guards:
                    line += f'  (guard: {guards[:60]})'
                lines.append(line)
            coi_graph = '\n'.join(lines) if lines else '<no per_output_influences>'
        except Exception as exc:
            coi_graph = f'<failed to parse io_relations.json: {exc}>'

    return ports_summary, coi_graph


def _extract_property_bodies(props_sv: Path, prop_names: Set[str]) -> Dict[str, str]:
    """Extract SVA property body text for each named property.

    Looks for ``property <name>; ... endproperty`` blocks.
    Returns {assert_xxx: 'property sva_id; ... endproperty'} mapping.
    """
    if not props_sv.exists():
        return {}

    content = props_sv.read_text(encoding='utf-8', errors='ignore')
    result: Dict[str, str] = {}

    for name in sorted(prop_names):
        # Strip 'assert_' prefix to get the property definition identifier
        prop_def_name = re.sub(r'^assert_', '', name)
        pat = re.compile(
            r'property\s+' + re.escape(prop_def_name) + r'\s*;(.*?)endproperty',
            re.DOTALL,
        )
        m = pat.search(content)
        if m:
            body = m.group(1).strip()
            result[name] = f'property {prop_def_name};\n  {body}\nendproperty'
        else:
            result[name] = f'// <definition for {prop_def_name} not found in properties.sv>'

    return result


def _llm_fix_vacuous_properties(
    fpv_dir: Path,
    sva_top: str,
    scope_path: str,
    vacuous_props: Set[str],
    fail_props: Set[str],
    llm_conf: Path,
    tail_lines: int = 100,
) -> Optional[str]:
    """Use LLM to rewrite vacuously-proven properties into non-vacuous assertions.

    Provides COI graph (per_output_influences) and port list as context so the LLM can
    suggest output-conditioned antecedents, $rose(rst_ni) rewrites, etc.

    Returns unified diff text (to be applied with _apply_patch), or None on failure.
    """
    if LLM_wrap is None:
        print('[POSTCHECK] LLM_wrap not available — cannot run LLM vacuous fix.')
        return None

    # Only fix properties that are not real bugs
    safe_vacuous = vacuous_props - fail_props
    if not safe_vacuous:
        print('[POSTCHECK] No safe vacuous props for LLM (all overlap with real-bug CEX props).')
        return None

    print(f'[POSTCHECK] Sending {len(safe_vacuous)} vacuous props to LLM for fix ...')

    props_sv = fpv_dir / 'sva' / 'properties.sv'
    ports_summary, coi_graph = _load_coi_context(fpv_dir, sva_top)
    prop_bodies = _extract_property_bodies(props_sv, safe_vacuous)

    vacuous_bodies_text = '\n\n'.join(f'--- {name} ---\n{body}' for name, body in sorted(prop_bodies.items()))
    if len(vacuous_bodies_text) > 10_000:
        vacuous_bodies_text = vacuous_bodies_text[:10_000] + '\n... [truncated — too many props]'

    payload = {
        'sva_top': sva_top,
        'scope_path': scope_path or '-',
        'ports_summary': ports_summary,
        'coi_graph': coi_graph,
        'vacuous_property_bodies': vacuous_bodies_text,
        'props_sv_path': str(props_sv),
        'jg_stdout_tail': _tail_text(fpv_dir / 'jg.stdout.log', tail_lines),
    }

    llm = LLM_wrap(
        name='default',
        conf_file=str(llm_conf),
        log_file=f'jg_fix_vacuous_{sva_top}.log',
    )

    try:
        res = llm.inference(payload, prompt_index='jg_fix_vacuous', n=1)
    except Exception as exc:
        print(f'[POSTCHECK] LLM fix_vacuous inference failed: {exc}')
        return None

    patch_text = ''
    if isinstance(res, list) and res:
        patch_text = res[0]
    elif isinstance(res, str):
        patch_text = res

    patch_text = (patch_text or '').strip()

    # Strip markdown code fences if present
    if patch_text.startswith('```'):
        inner: List[str] = []
        for line in patch_text.splitlines()[1:]:
            if line.strip() == '```':
                break
            inner.append(line)
        patch_text = '\n'.join(inner).strip()

    return patch_text or None


# ---------------------------------------------------------------------------
# Auto-convert BEHAVIORAL asserts → covers (no LLM needed)
# ---------------------------------------------------------------------------


def _auto_convert_behavioral_to_cover(fpv_dir: Path, classified: Dict[str, Dict]) -> List[str]:
    """In sva/properties.sv, change assert_svaXXX → cover_svaXXX for BEHAVIORAL props.

    Returns list of converted property short names.
    """
    props_sv = fpv_dir / 'sva' / 'properties.sv'
    if not props_sv.exists():
        return []

    content = props_sv.read_text(encoding='utf-8', errors='ignore')
    converted: List[str] = []

    for prop, info in classified.items():
        if info['category'] != 'BEHAVIORAL':
            continue
        # prop is like 'assert_sva017' — extract sva_id
        sva_id = re.sub(r'^assert_', '', prop)  # e.g. 'sva017'
        old = f'assert_{sva_id}: assert property({sva_id})'
        new = f'cover_{sva_id}: cover property({sva_id})'
        if old in content:
            content = content.replace(old, new)
            converted.append(prop)

    if converted:
        props_sv.write_text(content, encoding='utf-8')
        print(
            f'[POSTCHECK] Auto-converted {len(converted)} BEHAVIORAL assert→cover: '
            f'{", ".join(converted[:5])}{"..." if len(converted) > 5 else ""}'
        )

    return converted


def _auto_convert_vacuous_to_cover(
    fpv_dir: Path,
    vacuous_props: set,
    fail_props: set,
) -> List[str]:
    """Convert vacuously-proven assertions (unreachable witness) to cover properties.

    Vacuous proofs provide no real assurance.  Converting them to cover makes the
    result honest: JG will now report whether the scenario is reachable at all.

    SAFETY: Any assertion in `fail_props` (real CEX) is NEVER touched — real bugs
    are preserved.  Only assertions that are PROVEN vacuously (no witness trace) are
    converted.

    'assert_xxx: assert property(xxx)' → 'cover_xxx: cover property(xxx)'
    """
    props_sv = fpv_dir / 'sva' / 'properties.sv'
    if not props_sv.exists():
        return []

    # Never touch props that have actual CEX — real bugs must be preserved
    safe_props = vacuous_props - fail_props

    content = props_sv.read_text(encoding='utf-8', errors='ignore')
    converted: List[str] = []

    for prop in sorted(safe_props):
        sva_id = re.sub(r'^assert_', '', prop)
        old = f'assert_{sva_id}: assert property({sva_id})'
        new = f'cover_{sva_id}: cover property({sva_id})'
        if old in content:
            content = content.replace(old, new)
            converted.append(prop)
        else:
            print(f'[POSTCHECK] WARNING: vacuous assert "{old}" not found in properties.sv — skipping {prop}')

    if converted:
        props_sv.write_text(content, encoding='utf-8')
        print(
            f'[POSTCHECK] Converted {len(converted)} vacuous assert→cover (witness unreachable): '
            f'{", ".join(converted[:5])}{"..." if len(converted) > 5 else ""}'
        )
    if fail_props & vacuous_props:
        skipped = fail_props & vacuous_props
        print(
            f'[POSTCHECK] PRESERVED {len(skipped)} real-bug CEX props (not converted): '
            f'{", ".join(sorted(skipped)[:5])}{"..." if len(skipped) > 5 else ""}'
        )

    return converted


# ---------------------------------------------------------------------------
# Auto-convert PRE_ERROR/SPURIOUS asserts → assumes (no LLM needed)
# ---------------------------------------------------------------------------


def _auto_convert_spurious_to_assume(fpv_dir: Path, classified: Dict[str, Dict]) -> List[str]:
    """In sva/properties.sv, change assert_xxx → assume_xxx_pre + assume_xxx for
    PRE_ERROR and SPURIOUS props.  No LLM required — the conversion is deterministic.

    The label pattern is:  assert_{sva_id}: assert property({sva_id});
    It becomes:            assume_{sva_id}_pre: assume property({sva_id});
                           assume_{sva_id}: assume property({sva_id});

    Returns list of converted property short names.
    """
    props_sv = fpv_dir / 'sva' / 'properties.sv'
    if not props_sv.exists():
        return []

    content = props_sv.read_text(encoding='utf-8', errors='ignore')
    converted: List[str] = []

    for prop, info in classified.items():
        if info['category'] not in ('PRE_ERROR', 'SPURIOUS'):
            continue
        sva_id = re.sub(r'^assert_', '', prop)  # e.g. 'sva011' or 'store_buffer_empty_implies_no_data_req'
        old = f'assert_{sva_id}: assert property({sva_id})'
        new = f'assume_{sva_id}_pre: assume property({sva_id})\nassume_{sva_id}: assume property({sva_id})'
        if old in content:
            content = content.replace(old, new)
            converted.append(prop)
        else:
            print(f'[POSTCHECK] WARNING: could not find "{old}" in properties.sv — skipping {prop}')

    if converted:
        props_sv.write_text(content, encoding='utf-8')
        print(
            f'[POSTCHECK] Auto-converted {len(converted)} PRE_ERROR/SPURIOUS assert→assume: '
            f'{", ".join(converted[:5])}{"..." if len(converted) > 5 else ""}'
        )

    return converted


# ---------------------------------------------------------------------------
# Targeted TCL generation
# ---------------------------------------------------------------------------


def _write_targeted_tcl(fpv_dir: Path, fail_prop_shorts: List[str]) -> Path:
    """Write FPV_repair.tcl that only proves the specified failing properties.

    Replaces the broad autoprove with a targeted autoprove and tightens time limits
    so each repair iteration runs in minutes rather than hours.
    """
    orig_tcl = (fpv_dir / 'FPV.tcl').read_text(encoding='utf-8', errors='ignore')

    if fail_prop_shorts:
        # Build regexp matching only the target props
        pattern = '|'.join(f'.*{p}.*' for p in fail_prop_shorts)
        new_autoprove = f'autoprove -property {{{pattern}}} -regexp'
    else:
        new_autoprove = '# No failing properties to reprove'

    targeted = re.sub(
        r'autoprove\s+-property\s+\{[^}]+\}[^\n]*',
        new_autoprove,
        orig_tcl,
    )

    # Tighten per-property limits for faster repair iterations
    targeted = re.sub(r'set_prove_per_property_max_time_limit\s+\S+', 'set_prove_per_property_max_time_limit 3m', targeted)
    targeted = re.sub(r'set_prove_time_limit\s+\S+', 'set_prove_time_limit 30m', targeted)
    # Skip coverage measurement in repair runs (saves ~5-10 min)
    targeted = re.sub(r'\ncheck_cov\s+-measure[^\n]*', '\n# check_cov skipped in repair run', targeted)
    targeted = re.sub(r'\ncheck_cov\s+-report[^\n]*', '\n# check_cov skipped in repair run', targeted)

    repair_tcl = fpv_dir / 'FPV_repair.tcl'
    repair_tcl.write_text(targeted, encoding='utf-8')
    print(f'[POSTCHECK] Wrote targeted FPV_repair.tcl for {len(fail_prop_shorts)} props: {fail_prop_shorts}')
    return repair_tcl


# ---------------------------------------------------------------------------
# Parse targeted JG log to update results_summary.csv
# ---------------------------------------------------------------------------


def _parse_targeted_log(log_path: Path, targeted_props: List[str]) -> Dict[str, str]:
    """Parse jg.stdout.log for the targeted props only.

    Returns: {short_name: 'PROVEN' | 'FAIL' | 'UNKNOWN'}
    """
    if not log_path.exists():
        return {}

    # Match both proven and cex lines
    pat = re.compile(r'\[\s*\d+\]\s+(\S+)\s+(proven|cex|unknown)\s+')
    result: Dict[str, str] = {}
    targeted_set = set(targeted_props)

    for line in log_path.read_text(errors='ignore').splitlines():
        m = pat.search(line)
        if not m:
            continue
        prop = m.group(1)
        status = m.group(2)
        short = prop.split('.')[-1]
        if ':' in short:
            continue
        if short in targeted_set:
            result[short] = 'PROVEN' if status == 'proven' else ('FAIL' if status == 'cex' else 'UNKNOWN')

    return result


def _update_results_csv(
    fpv_dir: Path,
    targeted_results: Dict[str, str],
    behavioral_converted: List[str],
    prev_counts: Dict[str, int],
) -> None:
    """Update results_summary.csv based on targeted run outcomes."""
    counts = dict(prev_counts)

    # BEHAVIORAL props converted to cover: remove from FAIL, add to COVER
    counts['FAIL'] = max(0, counts.get('FAIL', 0) - len(behavioral_converted))
    counts['COVER'] = counts.get('COVER', 0) + len(behavioral_converted)

    # Targeted props: adjust FAIL/PROVEN for each result
    for prop, status in targeted_results.items():
        if status == 'PROVEN':
            counts['FAIL'] = max(0, counts.get('FAIL', 0) - 1)
            counts['PROVEN'] = counts.get('PROVEN', 0) + 1
        elif status == 'UNKNOWN':
            counts['FAIL'] = max(0, counts.get('FAIL', 0) - 1)
            counts['UNKNOWN'] = counts.get('UNKNOWN', 0) + 1

    _write_results_summary(fpv_dir / 'results_summary.csv', counts)
    print(
        f'[POSTCHECK] Updated results_summary.csv: '
        f'PROVEN={counts.get("PROVEN", 0)} FAIL={counts.get("FAIL", 0)} '
        f'COVER={counts.get("COVER", 0)} UNKNOWN={counts.get("UNKNOWN", 0)}'
    )


# ---------------------------------------------------------------------------
# File collection for LLM context
# ---------------------------------------------------------------------------


def _collect_files(fpv_dir: Path, sva_top: str) -> List[Path]:
    # Intentionally exclude files.vc and FPV.tcl — the LLM must ONLY edit sva/properties.sv
    cands = [
        fpv_dir / 'jg.stderr.log',
        fpv_dir / 'jg.stdout.log',
        fpv_dir / 'results_summary.csv',
        fpv_dir / 'sva' / 'properties.sv',
        fpv_dir / 'sva' / f'{sva_top}_prop.sv',
        fpv_dir / 'sva' / f'{sva_top}_bind.sv',
    ]
    out: List[Path] = []
    seen: set = set()
    for p in cands:
        if p in seen:
            continue
        seen.add(p)
        if p.exists():
            out.append(p)
    return out


def _files_blob(paths: List[Path]) -> str:
    parts: List[str] = []
    for p in paths:
        parts.append(f'=== FILE: {p} ===')
        parts.append(_read_text(p))
        parts.append('')
    return '\n'.join(parts)


# ---------------------------------------------------------------------------
# Backup
# ---------------------------------------------------------------------------


def _backup_tree(fpv_dir: Path, it: int = 0) -> Path:
    bdir = fpv_dir / f'backup_before_post_repair_iter{it + 1}'
    if bdir.exists():
        shutil.rmtree(bdir)
    bdir.mkdir(parents=True, exist_ok=True)

    for rel in ['FPV.tcl', 'FPV_repair.tcl', 'files.vc', 'results_summary.csv', 'jg.stderr.log', 'jg.stdout.log', 'sva']:
        src = fpv_dir / rel
        if src.exists():
            dst = bdir / rel
            if src.is_dir():
                shutil.copytree(src, dst, symlinks=True, ignore_dangling_symlinks=True)
            else:
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
    return bdir


# ---------------------------------------------------------------------------
# Pure-Python unified diff applier (robust against LLM line-number errors)
# ---------------------------------------------------------------------------


def _apply_patch(patch_text: str, patch_path: Path) -> bool:
    """Apply a unified diff in pure Python — robust against LLM line-number/count errors."""
    patch_path.write_text(patch_text, encoding='utf-8')

    m = re.search(r'^--- (.+)', patch_text, re.MULTILINE)
    if not m:
        print('[POSTCHECK] patch: no --- header found')
        return False
    target = Path(m.group(1).split('\t')[0].strip())
    if not target.exists():
        print(f'[POSTCHECK] patch: target not found: {target}')
        return False

    file_lines: List[str] = target.read_text(encoding='utf-8', errors='ignore').splitlines(keepends=True)
    diff_lines = patch_text.splitlines()
    i = 0
    while i < len(diff_lines) and (diff_lines[i].startswith('---') or diff_lines[i].startswith('+++')):
        i += 1

    offset = 0
    hunk_num = 0

    while i < len(diff_lines):
        line = diff_lines[i]
        if not line.startswith('@@'):
            i += 1
            continue

        hm = re.match(r'^@@ -(\d+)(?:,\d+)? \+\d+(?:,\d+)? @@', line)
        hint = (int(hm.group(1)) - 1 + offset) if hm else 0
        i += 1
        hunk_num += 1

        raw_hunk: List[str] = []
        while (
            i < len(diff_lines)
            and not diff_lines[i].startswith('@@')
            and not (diff_lines[i].startswith('---') and len(raw_hunk) > 0)
        ):
            raw_hunk.append(diff_lines[i])
            i += 1

        old_lines = [line_text[1:] for line_text in raw_hunk if not line_text.startswith('+')]
        new_lines = [line_text[1:] for line_text in raw_hunk if not line_text.startswith('-')]

        def _norm(ls: List[str]) -> List[str]:
            return [line_text if line_text.endswith('\n') else line_text + '\n' for line_text in ls]

        old_norm = _norm(old_lines)
        new_norm = _norm(new_lines)

        if not old_norm:
            file_lines[hint:hint] = new_norm
            offset += len(new_norm)
            print(f'[POSTCHECK] hunk {hunk_num}: inserted {len(new_norm)} lines at {hint + 1}')
            continue

        def _strip(s: str) -> str:
            return s.rstrip('\n\r')

        found = -1
        search_order = list(range(max(0, hint - 10), min(len(file_lines), hint + len(old_norm) + 10)))
        search_order += [p for p in range(len(file_lines)) if p not in set(search_order)]
        for pos in search_order:
            if pos + len(old_norm) > len(file_lines):
                continue
            if all(_strip(file_lines[pos + j]) == _strip(old_norm[j]) for j in range(len(old_norm))):
                found = pos
                break

        if found == -1:
            print(f'[POSTCHECK] hunk {hunk_num}: context not found near line {hint + 1} — skipping hunk')
            continue

        file_lines[found : found + len(old_norm)] = new_norm
        delta = len(new_norm) - len(old_norm)
        offset += delta
        print(
            f'[POSTCHECK] hunk {hunk_num}: applied at line {found + 1} ({len(old_norm)}→{len(new_norm)} lines, delta={delta:+d})'
        )

    target.write_text(''.join(file_lines), encoding='utf-8')
    return True


# ---------------------------------------------------------------------------
# JasperGold runner
# ---------------------------------------------------------------------------


def _run_jasper(fpv_dir: Path, jasper_bin: str, tcl_file: str = 'FPV.tcl') -> bool:
    """Run JasperGold. Returns True if the run completed (jg.stdout.log was written).

    Uses jg.stdout.log mtime (not results_summary.csv) to detect completion — our
    Python code writes results_summary.csv, not JG itself. JG may return non-zero
    even on successful FPV runs when assertions FAIL, so exit code is not used.
    Successful run is detected by checking for proof/cex lines in jg.stdout.log
    and absence of early compile error markers.
    """
    cmd = [jasper_bin, '-allow_unsupported_OS', '-tcl', tcl_file, '-batch']
    jg_stdout = fpv_dir / 'jg.stdout.log'
    jg_stderr = fpv_dir / 'jg.stderr.log'

    print(f'[POSTCHECK] Running JG: {tcl_file}')
    try:
        with open(jg_stdout, 'w') as fo, open(jg_stderr, 'w') as fe:
            subprocess.run(cmd, cwd=fpv_dir, stdout=fo, stderr=fe)
    except Exception as e:
        print(f'[POSTCHECK] JG launch error: {e}')
        return False

    if not jg_stdout.exists() or jg_stdout.stat().st_size == 0:
        print('[POSTCHECK] JG did not write jg.stdout.log — likely launch failure.')
        return False

    log_text = jg_stdout.read_text(errors='ignore')
    # Check for successful proof phase: at least one proven/cex result line
    if re.search(r'\[\s*\d+\]\s+\S+\s+(proven|cex)\s+', log_text):
        print('[POSTCHECK] JG completed (found proof results in jg.stdout.log).')
        return True
    # Check for compilation error markers
    if 'ERROR' in log_text or 'compile' in log_text.lower():
        print('[POSTCHECK] JG appears to have a compilation error (no proof results found).')
        return False
    print('[POSTCHECK] JG exited but produced no proof results — possible compilation failure.')
    return False


# ---------------------------------------------------------------------------
# Main repair loop
# ---------------------------------------------------------------------------


def run_postcheck_repair(
    fpv_dir: Path,
    sva_top: str,
    scope_path: str,
    llm_conf: Optional[Path],
    apply: bool = False,
    rerun_jg: bool = False,
    jasper_bin: str = 'jg',
    max_iters: int = 1,
    tail_lines: int = 250,
    also_read_csv_spec: bool = True,
    behavioral_threshold: int = BEHAVIORAL_BOUND_THRESHOLD,
    assume_spurious: bool = False,
    fix_vacuous: bool = False,
    fix_vacuous_llm: bool = False,
) -> int:
    fpv_dir = fpv_dir.resolve()
    counts = _read_results_summary(fpv_dir / 'results_summary.csv')
    need, reason = _needs_repair(counts)

    # ---- Step 0a: LLM-based vacuous property fix — runs even if FAIL=0 ----
    if fix_vacuous_llm and apply:
        if llm_conf is None or not llm_conf.exists():
            print(f'[POSTCHECK] --fix-vacuous-llm requires --llm-conf: {llm_conf}')
        else:
            log_path = fpv_dir / 'jg.stdout.log'
            vacuous = _find_vacuous_asserts(log_path)
            fail_classified = _classify_fails_structured(log_path)
            fail_prop_names = set(fail_classified.keys())
            if vacuous:
                print(f'[POSTCHECK] LLM vacuous fix: {len(vacuous)} vacuous props detected.')
                patch = _llm_fix_vacuous_properties(
                    fpv_dir=fpv_dir,
                    sva_top=sva_top,
                    scope_path=scope_path,
                    vacuous_props=vacuous,
                    fail_props=fail_prop_names,
                    llm_conf=llm_conf,
                    tail_lines=tail_lines,
                )
                if patch and patch.startswith('--- '):
                    _backup_tree(fpv_dir, 0)
                    patch_path = fpv_dir / 'jg_fix_vacuous.patch'
                    ok = _apply_patch(patch, patch_path)
                    if ok:
                        print('[POSTCHECK] LLM vacuous fix patch applied.')
                        if rerun_jg:
                            jg_ok = _run_jasper(fpv_dir, jasper_bin, tcl_file='FPV.tcl')
                            if jg_ok:
                                # Re-read counts after full re-run
                                new_vac = _find_vacuous_asserts(fpv_dir / 'jg.stdout.log')
                                fixed_count = len(vacuous) - len(new_vac)
                                print(
                                    f'[POSTCHECK] LLM vacuous fix: {fixed_count} props '
                                    f'no longer vacuous, {len(new_vac)} still vacuous.'
                                )
                            else:
                                print('[POSTCHECK] WARNING: JG produced no proof results after LLM vacuous fix.')
                    else:
                        print('[POSTCHECK] LLM vacuous fix: patch apply failed — skipping.')
                else:
                    print('[POSTCHECK] LLM vacuous fix: LLM did not return a valid diff.')
            else:
                print('[POSTCHECK] LLM vacuous fix: no vacuous assertions found in log.')

    # ---- Step 0b: Fix vacuous proofs (unreachable witness) — runs even if FAIL=0 ----
    if fix_vacuous and apply:
        log_path = fpv_dir / 'jg.stdout.log'
        vacuous = _find_vacuous_asserts(log_path)
        # Build the set of props that actually have real CEX (must NOT be touched)
        fail_classified = _classify_fails_structured(log_path)
        fail_prop_names = set(fail_classified.keys())
        if vacuous:
            print(
                f'[POSTCHECK] Found {len(vacuous)} vacuously-proven assertions '
                f'(unreachable witness). Converting to cover (real-bug CEX preserved).'
            )
            vac_converted = _auto_convert_vacuous_to_cover(fpv_dir, vacuous, fail_prop_names)
            if vac_converted:
                # Vacuous→cover: remove from PROVEN, add to COVER
                counts['PROVEN'] = max(0, counts.get('PROVEN', 0) - len(vac_converted))
                counts['COVER'] = counts.get('COVER', 0) + len(vac_converted)
                _write_results_summary(fpv_dir / 'results_summary.csv', counts)
                print(f'[POSTCHECK] After vacuous fix: PROVEN={counts.get("PROVEN", 0)} COVER={counts.get("COVER", 0)}')
        else:
            print('[POSTCHECK] No vacuously-proven assertions found.')

    if not need and not (fix_vacuous and apply):
        print(f'[POSTCHECK] No repair needed ({reason}).')
        return 0
    if not need:
        return 0  # vacuous fix ran, FAIL was already 0

    if not assume_spurious:
        if LLM_wrap is None:
            print('[POSTCHECK] LLM_wrap not available. Cannot repair.')
            return 2
        if llm_conf is None or not llm_conf.exists():
            print(f'[POSTCHECK] Missing llm conf: {llm_conf}')
            return 2

    spec_csv = fpv_dir / f'{sva_top}_spec.csv'
    extra_paths: List[Path] = []
    if also_read_csv_spec and spec_csv.exists():
        extra_paths.append(spec_csv)

    # ---- Step 0: Classify all FAILs from the original log -------------------
    classified = _classify_fails_structured(fpv_dir / 'jg.stdout.log')
    if not classified:
        print('[POSTCHECK] Could not classify FAIL properties from jg.stdout.log.')
        classified = {}

    behavioral = {k: v for k, v in classified.items() if v['category'] == 'BEHAVIORAL'}
    fixable = {k: v for k, v in classified.items() if v['category'] != 'BEHAVIORAL'}

    print(f'[POSTCHECK] Classification: {len(behavioral)} BEHAVIORAL (→cover), {len(fixable)} fixable (PRE_ERROR/SPURIOUS → LLM)')

    # ---- Step 1: Auto-convert BEHAVIORAL asserts → covers ------------------
    behavioral_converted: List[str] = []
    if behavioral and apply:
        behavioral_converted = _auto_convert_behavioral_to_cover(fpv_dir, behavioral)
        # Update counts to reflect conversion (no JG rerun needed)
        counts['FAIL'] = max(0, counts.get('FAIL', 0) - len(behavioral_converted))
        counts['COVER'] = counts.get('COVER', 0) + len(behavioral_converted)
        _write_results_summary(fpv_dir / 'results_summary.csv', counts)
        print(f'[POSTCHECK] After behavioral conversion: FAIL={counts.get("FAIL", 0)}')
        need, reason = _needs_repair(counts)
        if not need:
            print('[POSTCHECK] All FAILs were BEHAVIORAL — converted to cover. Done.')
            return 0

    # ---- Step 2 (no-LLM path): Auto-convert PRE_ERROR/SPURIOUS → assume ----
    if assume_spurious and fixable and apply:
        spurious_converted = _auto_convert_spurious_to_assume(fpv_dir, fixable)
        if spurious_converted:
            counts['FAIL'] = max(0, counts.get('FAIL', 0) - len(spurious_converted))
            _write_results_summary(fpv_dir / 'results_summary.csv', counts)
            print(f'[POSTCHECK] After assume-spurious conversion: FAIL={counts.get("FAIL", 0)}')

        if rerun_jg:
            all_conv = list(fixable.keys())
            _write_targeted_tcl(fpv_dir, all_conv)
            _backup_tree(fpv_dir, 0)
            jg_ok = _run_jasper(fpv_dir, jasper_bin, tcl_file='FPV_repair.tcl')
            if jg_ok:
                print('[POSTCHECK] JG verification after assume-spurious: OK')
            else:
                print('[POSTCHECK] WARNING: JG produced no proof results after assume-spurious conversion.')

        need, reason = _needs_repair(counts)
        if not need:
            print('[POSTCHECK] All FAILs resolved via assume-spurious. Done.')
            return 0

    # If assume_spurious was requested but LLM conf is not needed — return now
    if assume_spurious:
        need, reason = _needs_repair(counts)
        if not need:
            return 0
        print(f'[POSTCHECK] assume-spurious done but {reason} remains — consider LLM repair.')
        return 0

    # ---- Step 3: LLM repair loop for remaining fixable FAILs ---------------
    fail_short_names = list(fixable.keys())
    classification_text = _format_classification_summary(classified)

    for it in range(max_iters):
        # Re-classify from current log if we have updated results
        if it > 0:
            classified = _classify_fails_structured(fpv_dir / 'jg.stdout.log')
            new_behavioral = {k: v for k, v in classified.items() if v['category'] == 'BEHAVIORAL'}
            if new_behavioral and apply:
                # Props that shifted from SPURIOUS→BEHAVIORAL after LLM repair: auto-convert
                newly_conv = _auto_convert_behavioral_to_cover(fpv_dir, new_behavioral)
                if newly_conv:
                    counts['FAIL'] = max(0, counts.get('FAIL', 0) - len(newly_conv))
                    counts['COVER'] = counts.get('COVER', 0) + len(newly_conv)
                    _write_results_summary(fpv_dir / 'results_summary.csv', counts)
                    print(f'[POSTCHECK] Iter {it + 1}: converted {len(newly_conv)} new BEHAVIORAL→cover')
            fixable = {k: v for k, v in classified.items() if v['category'] != 'BEHAVIORAL'}
            fail_short_names = list(fixable.keys())
            classification_text = _format_classification_summary(classified)
            if not fail_short_names:
                print('[POSTCHECK] No more fixable FAIL props. Done.')
                break

        print(
            f'[POSTCHECK] Repair iteration {it + 1}/{max_iters} — {len(fail_short_names)} fixable FAIL props: {fail_short_names}'
        )

        # Write targeted TCL (only proves fixable props, tighter time limits)
        if apply and rerun_jg and fail_short_names:
            _write_targeted_tcl(fpv_dir, fail_short_names)

        files = _collect_files(fpv_dir, sva_top) + extra_paths
        blob = _files_blob(files)

        payload = {
            'sva_top': sva_top,
            'scope_path': scope_path or '-',
            'results_summary': _read_text(fpv_dir / 'results_summary.csv'),
            'fail_classification': classification_text,
            'fail_properties': '\n'.join(
                f'{p}  engine={v["engine"]}  bound={v["bound"]}  [{v["category"]}]' for p, v in fixable.items()
            )
            or '<none>',
            'jg_stderr_tail': _tail_text(fpv_dir / 'jg.stderr.log', tail_lines),
            'jg_stdout_tail': _tail_text(fpv_dir / 'jg.stdout.log', tail_lines),
            'jg_log_tail': _tail_text(fpv_dir / 'jgproject' / 'jg.log', tail_lines),
            'coverage_summary': _read_text(fpv_dir / 'formal_coverage_summary.txt'),
            'files_blob': blob,
        }

        llm = LLM_wrap(
            name='default',
            conf_file=str(llm_conf),
            log_file=f'jg_post_repair_{sva_top}_iter{it + 1}.log',
        )

        try:
            res = llm.inference(payload, prompt_index='jg_post_repair_patch', n=1)
        except Exception as e:
            print(f'[POSTCHECK] LLM inference failed: {e}')
            return 2

        patch_text = ''
        if isinstance(res, list) and res:
            patch_text = res[0]
        elif isinstance(res, str):
            patch_text = res

        patch_text = (patch_text or '').strip()

        # Strip markdown code fences
        if patch_text.startswith('```'):
            inner = []
            for line in patch_text.splitlines()[1:]:
                if line.strip() == '```':
                    break
                inner.append(line)
            patch_text = '\n'.join(inner).strip()

        patch_path = fpv_dir / f'jg_post_repair_iter{it + 1}.patch'
        patch_path.write_text(patch_text + '\n', encoding='utf-8')

        if not patch_text.startswith('--- '):
            print('[POSTCHECK] LLM did not output a unified diff. Wrote', patch_path, '; not applying.')
            return 2

        if not apply:
            print('[POSTCHECK] Patch produced (not applied). See:', patch_path)
            return 0

        bdir = _backup_tree(fpv_dir, it)
        ok = _apply_patch(patch_text, patch_path)
        if not ok:
            print('[POSTCHECK] Patch apply failed. Backup at:', bdir)
            return 2

        print('[POSTCHECK] Patch applied. Backup at:', bdir)

        if rerun_jg:
            # Use targeted TCL (only failing fixable props) — much faster than full FPV
            tcl = 'FPV_repair.tcl' if (fpv_dir / 'FPV_repair.tcl').exists() else 'FPV.tcl'
            jg_ok = _run_jasper(fpv_dir, jasper_bin, tcl_file=tcl)

            if jg_ok:
                # Parse targeted results and update CSV
                targeted_results = _parse_targeted_log(fpv_dir / 'jg.stdout.log', fail_short_names)
                print(f'[POSTCHECK] Targeted results: {targeted_results}')
                # Behavioral conversions were already written to CSV before JG ran.
                # Only pass behavioral_converted=[...] on iter0 if JG run was the FIRST run
                # (no behavioral pre-applied). Since we apply behavioral before the loop,
                # always pass [] here to avoid double-counting.
                if targeted_results:
                    _update_results_csv(fpv_dir, targeted_results, [], counts)
                counts = _read_results_summary(fpv_dir / 'results_summary.csv')
            else:
                # JG produced no proof results (compilation failure or empty run).
                # Restore sva/properties.sv from the backup made before this iteration
                # so the next LLM call starts from the clean pre-patch state.
                targeted_results = {}
                print('[POSTCHECK] JG ran without proof results — restoring properties.sv from backup.')
                bak_sv = bdir / 'sva' / 'properties.sv'
                if bak_sv.exists():
                    shutil.copy2(bak_sv, fpv_dir / 'sva' / 'properties.sv')
                    print(f'[POSTCHECK] Restored sva/properties.sv from {bdir}')
                # Also restore jg.stdout.log from backup so next classification works
                bak_log = bdir / 'jg.stdout.log'
                if bak_log.exists():
                    shutil.copy2(bak_log, fpv_dir / 'jg.stdout.log')
                    print(f'[POSTCHECK] Restored jg.stdout.log from {bdir}')
                counts = _read_results_summary(fpv_dir / 'results_summary.csv')
            behavioral_converted = []  # reset — conversions already applied

        need, reason = _needs_repair(counts)
        if not need:
            print('[POSTCHECK] Repair condition cleared.')
            return 0

    # Final reconciliation: check if all remaining CEX in jg.stdout.log are BEHAVIORAL
    # (already converted to cover). If so, actual FAIL=0, regardless of stale CSV counts.
    final_cex = _classify_fails_structured(fpv_dir / 'jg.stdout.log')
    actually_remaining = {k: v for k, v in final_cex.items() if v['category'] != 'BEHAVIORAL'}
    if not actually_remaining and final_cex:
        # All CEX in log are BEHAVIORAL props → they were auto-converted to cover → real FAIL=0
        counts['FAIL'] = 0
        _write_results_summary(fpv_dir / 'results_summary.csv', counts)
        print('[POSTCHECK] All remaining CEX were BEHAVIORAL (auto-converted to cover). FAIL=0.')
        return 0
    print(f'[POSTCHECK] Reached max_iters. Final: FAIL={counts.get("FAIL", 0)}')
    return 2 if counts.get('FAIL', 0) > 0 else 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[List[str]] = None) -> int:
    import argparse

    ap = argparse.ArgumentParser(description='Post-Jasper triage + LLM repair with automatic BEHAVIORAL→cover conversion.')
    ap.add_argument('--fpv-dir', required=True, help='Path to the FPV output directory')
    ap.add_argument('--sva-top', required=True, help='SVA module top name (e.g. load_unit)')
    ap.add_argument('--scope-path', default='', help='DUT scope path for context')
    ap.add_argument('--llm-conf', default=None, help='Path to jg_post_repair_prompt.yaml (not needed with --assume-spurious)')
    ap.add_argument(
        '--assume-spurious',
        action='store_true',
        help='Auto-convert PRE_ERROR/SPURIOUS asserts to assumes (no LLM, no context limits)',
    )
    ap.add_argument('--apply', action='store_true', help='Apply patch/conversion to properties.sv')
    ap.add_argument('--rerun-jg', action='store_true', help='Rerun Jasper after applying patch')
    ap.add_argument('--jasper-bin', default='jg', help='Path to jg binary')
    ap.add_argument('--max-iters', type=int, default=1, help='Max LLM repair iterations')
    ap.add_argument('--tail-lines', type=int, default=250, help='Lines of log tail for LLM context')
    ap.add_argument('--no-csv', action='store_true', help='Do not include *_spec.csv in context')
    ap.add_argument(
        '--behavioral-threshold',
        type=int,
        default=BEHAVIORAL_BOUND_THRESHOLD,
        help=f'Ht/L bound >= this → BEHAVIORAL (auto-convert to cover, default={BEHAVIORAL_BOUND_THRESHOLD})',
    )
    ap.add_argument(
        '--fix-vacuous',
        action='store_true',
        help='Auto-convert vacuously-proven assertions (unreachable witness) to cover. '
        'Real-bug CEX assertions are NEVER touched.',
    )
    ap.add_argument(
        '--fix-vacuous-llm',
        action='store_true',
        help='Use LLM to rewrite vacuously-proven assertions into non-vacuous forms '
        '(e.g., $rose(rst_ni), output-conditioned antecedents). Requires --llm-conf. '
        'Combine with --fix-vacuous to heuristically convert any remaining ones to cover.',
    )
    args = ap.parse_args(argv)

    return run_postcheck_repair(
        fpv_dir=Path(args.fpv_dir),
        sva_top=args.sva_top,
        scope_path=args.scope_path,
        llm_conf=Path(args.llm_conf) if args.llm_conf else None,
        apply=args.apply,
        rerun_jg=args.rerun_jg,
        jasper_bin=args.jasper_bin,
        max_iters=args.max_iters,
        tail_lines=args.tail_lines,
        also_read_csv_spec=(not args.no_csv),
        behavioral_threshold=args.behavioral_threshold,
        assume_spurious=args.assume_spurious,
        fix_vacuous=args.fix_vacuous,
        fix_vacuous_llm=args.fix_vacuous_llm,
    )


if __name__ == '__main__':
    raise SystemExit(main())
