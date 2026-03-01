#!/usr/bin/env python3
"""
cli_bug_detect.py  –  CVA6 Bug Detection: GitHub issues × FPV properties × Mutations.

Three detection modes (combinable):
  1. GitHub Issue Cross-Reference  — fetch open CVA6 bugs → classify against FPV results
  2. Multi-model scan              — --scan-all combines gpt51 + gpt53codex results
  3. Random Mutation Testing       -- --mutate injects random RTL bugs, checks if
                                      existing properties catch them (mutation score)

Coverage classifications:
  DETECTED         — FAIL property matching bug signals found
  POSSIBLY_COVERED — PROVEN property matches bug scenario
  PROPERTY_GAP     — Module tested, no relevant property found
  MODULE_NOT_TESTED— Responsible module not in any FPV run
  NOT_APPLICABLE   — Bug outside all tested module areas

Usage:
  # GitHub cross-reference (all models combined):
  uv run python3 hagent/tool/cli_bug_detect.py \\
      --out-dir $HAGENT_BUILD_DIR --scan-all --html-out /tmp/bugs.html

  # Add random mutation testing for load_unit + store_unit:
  uv run python3 hagent/tool/cli_bug_detect.py \\
      --out-dir $HAGENT_BUILD_DIR --scan-all \\
      --mutate --rtl-dir $CVA6_REPO_DIR/core \\
      --mutate-modules load_unit,store_unit \\
      --num-mutations 15 --jasper-bin $JASPER_BIN \\
      --html-out /tmp/bugs.html
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

# ── RTL file locations relative to CVA6 core dir ─────────────────────────────
# Used for --mutate mode to find the RTL file for each module.

MODULE_RTL_PATHS: dict[str, str] = {
    'load_unit': 'load_unit.sv',
    'store_unit': 'store_unit.sv',
    'wt_dcache': 'cache_subsystem/wt_dcache.sv',
    'cva6_icache': 'cache_subsystem/cva6_icache.sv',
    'id_stage': 'id_stage.sv',
    'issue_stage': 'issue_stage.sv',
    'aes': 'aes.sv',
    'pmp': 'pmp/src/pmp.sv',
    'decoder': 'decoder.sv',
}


# ── CVA6 module → functionality keywords ──────────────────────────────────────

MODULE_RESPONSIBILITIES: dict[str, list[str]] = {
    'load_unit': [
        'load',
        'lbu',
        'lhu',
        'lw',
        'ld',
        'lbuff',
        'load_buffer',
        'trans_id',
        'transaction_id',
        'dtlb',
        'page_fault',
        'misalign',
        'misaligned',
        'scause',
        'mcause',
        'page_offset',
        'pop_ld',
    ],
    'store_unit': [
        'store',
        'sw',
        'sd',
        'sb',
        'sh',
        'fsw',
        'write',
        'store_unit',
        'pmp',
        'access_fault',
        'misalign',
        'misaligned',
        'mcause',
        'scause',
        'store_buffer',
        'wbuffer',
        'commit_store',
    ],
    'issue_stage': [
        'scoreboard',
        'forward',
        'forwarding',
        'issue',
        'commit',
        'operand',
        'meltdown',
        'speculative',
        'transient',
        'exception_pending',
        'issue_read_operands',
        'issue_stage',
    ],
    'id_stage': [
        'decode',
        'decoder',
        'illegal',
        'instruction',
        'hfence',
        'fence',
        'id_stage',
        'compressed',
        'rvc',
        'zba',
        'zbb',
        'zbc',
    ],
    'wt_dcache': [
        'dcache',
        'cache',
        'write_through',
        'miss',
        'hit',
        'evict',
        'wt_dcache',
        'cache_subsystem',
        'cacheline',
        'writeback',
    ],
    'cva6_icache': [
        'icache',
        'fetch',
        'instruction_cache',
        'prefetch',
        'cache_invalidate',
        'cva6_icache',
    ],
    'aes': [
        'aes',
        'aes32',
        'aes32esi',
        'aes32esmi',
        'aes32dsi',
        'aes32dsmi',
        'zkn',
        'zkne',
        'zknd',
        'crypto',
        'cipher',
        'encryption',
    ],
    'pmp': [
        'pmp',
        'physical_memory_protection',
        'locked',
        'napot',
        'tor',
        'priority',
        'access_fault',
        'pmp_entry',
    ],
}

# Modules we know are NOT yet tested (for classification)
_UNTESTED_MODULES = {'pmp', 'csr_regfile', 'commit_stage', 'fpu', 'ex_stage'}

# Stop-words to exclude from keyword extraction
_STOP_WORDS = {
    'the',
    'and',
    'not',
    'for',
    'with',
    'this',
    'that',
    'when',
    'from',
    'will',
    'should',
    'which',
    'where',
    'also',
    'into',
    'then',
    'does',
    'have',
    'has',
    'had',
    'been',
    'are',
    'was',
    'were',
    'can',
    'may',
    'but',
    'if',
    'is',
    'in',
    'on',
    'at',
    'or',
    'to',
    'a',
    'an',
    'issue',
    'bug',
    'error',
    'fix',
    'wrong',
    'incorrect',
    'fail',
    'fails',
    'problem',
    'value',
    'result',
    'case',
    'way',
    'set',
    'get',
    'check',
    'bit',
    'bits',
    'signal',
    'port',
    'logic',
    'reg',
    'wire',
    'cva6',
    'risc',
    'riscv',
    'cpu',
    'core',
    'design',
    'module',
    'block',
    'register',
    'inst',
    'instruction',
    'test',
    'testbench',
    'simulation',
    'verilog',
    'systemverilog',
    'rtl',
    'fpga',
    'asic',
    'when',
    'upon',
    'instead',
    'triggers',
    'causes',
    'expected',
    'actual',
    'behavior',
    'violation',
    'report',
    'reported',
    'correct',
    'correctly',
}

_SV_IDENT = re.compile(r'\b([a-z][a-z0-9_]{2,})\b', re.IGNORECASE)


def extract_keywords(text: str) -> set[str]:
    words = _SV_IDENT.findall(text.lower())
    return {w for w in words if w not in _STOP_WORDS and len(w) > 3}


# ── Coverage classification ────────────────────────────────────────────────────

DETECTED = 'DETECTED'  # FAIL property matching bug signals found
POSSIBLY_COVERED = 'POSSIBLY_COVERED'  # PROVEN property matches bug scenario
PROPERTY_GAP = 'PROPERTY_GAP'  # Module tested, no relevant property
MODULE_NOT_TESTED = 'MODULE_NOT_TESTED'  # Responsible module not in any FPV run
NOT_APPLICABLE = 'NOT_APPLICABLE'  # Bug outside all tested module areas


# ── Data classes ──────────────────────────────────────────────────────────────


@dataclass
class PropertyDetail:
    sid: str
    prop_type: str
    name: str
    scenario: str
    signals: str
    status: str = 'N/A'  # PROVEN / FAIL / UNREACHABLE / COVER / N/A
    cex_cycles: int = 0


@dataclass
class ModuleResult:
    module: str
    mode: str  # blackbox / whitebox
    model_tag: str  # e.g. "gpt51", "gpt53codex", or "" for legacy
    fpv_dir: Path
    summary: dict  # {PROVEN: N, FAIL: N, ...}
    properties: list[PropertyDetail] = field(default_factory=list)


@dataclass
class BugMatch:
    module: str
    mode: str
    model_tag: str
    property_name: str
    status: str
    score: int
    overlap_kw: list[str]


@dataclass
class BugCoverage:
    issue_number: int
    title: str
    url: str
    classification: str
    responsible_modules: list[str]
    tested_modules: list[str]
    top_matches: list[BugMatch]
    issue_keywords: list[str]


# ── GitHub API ────────────────────────────────────────────────────────────────

GITHUB_API = 'https://api.github.com'


def _gh_get(url: str, token: Optional[str] = None) -> dict | list:
    req = urllib.request.Request(url)
    req.add_header('Accept', 'application/vnd.github+json')
    req.add_header('X-GitHub-Api-Version', '2022-11-28')
    if token:
        req.add_header('Authorization', f'Bearer {token}')
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            return json.loads(resp.read())
    except urllib.error.HTTPError as e:
        body = e.read().decode('utf-8', errors='replace')
        print(f'[ERROR] GitHub API {url}: HTTP {e.code}: {body[:300]}', file=sys.stderr)
        return []
    except Exception as exc:
        print(f'[ERROR] GitHub API {url}: {exc}', file=sys.stderr)
        return []


def fetch_open_issues(
    owner: str,
    repo: str,
    token: Optional[str],
    label: str,
    max_issues: int,
) -> list[dict]:
    issues: list[dict] = []
    page = 1
    per_page = min(max_issues, 100)
    while len(issues) < max_issues:
        url = (
            f'{GITHUB_API}/repos/{owner}/{repo}/issues'
            f'?state=open&labels={urllib.parse.quote(label)}'  # type: ignore[attr-defined]
            f'&per_page={per_page}&page={page}'
        )
        batch = _gh_get(url, token)
        if not batch or not isinstance(batch, list):
            break
        batch = [i for i in batch if 'pull_request' not in i]
        issues.extend(batch)
        if len(batch) < per_page:
            break
        page += 1
    return issues[:max_issues]


# ── FPV result loading ────────────────────────────────────────────────────────

_JASPER_PROP_RE = re.compile(r'^\s*(?:PROVEN|FAIL|UNREACHABLE|COVER|UNKNOWN)\s+(\w+)', re.IGNORECASE)
_JASPER_CEX_RE = re.compile(r'CEX.*?(\d+)\s+cycles?', re.IGNORECASE)


def _load_jasper_status(fpv_dir: Path) -> dict[str, tuple[str, int]]:
    """Parse jg.stdout.log → {prop_name: (status, cex_cycles)}."""
    log = fpv_dir / 'jg.stdout.log'
    if not log.exists():
        return {}
    result: dict[str, tuple[str, int]] = {}
    current_prop: Optional[str] = None
    for line in log.read_text(errors='replace').splitlines():
        m = _JASPER_PROP_RE.match(line)
        if m:
            status = line.strip().split()[0].upper()
            current_prop = m.group(1)
            result[current_prop] = (status, 0)
        elif current_prop and 'CEX' in line.upper():
            cm = _JASPER_CEX_RE.search(line)
            if cm:
                prev_status = result[current_prop][0]
                result[current_prop] = (prev_status, int(cm.group(1)))
    return result


def _load_spec_csv(fpv_dir: Path, module: str) -> list[PropertyDetail]:
    """Load <module>_spec.csv for rich property metadata."""
    csv_path = fpv_dir / f'{module}_spec.csv'
    if not csv_path.exists():
        return []
    props: list[PropertyDetail] = []
    try:
        with csv_path.open(newline='', encoding='utf-8', errors='replace') as f:
            reader = csv.DictReader(f)
            for row in reader:
                props.append(
                    PropertyDetail(
                        sid=row.get('sid', ''),
                        prop_type=row.get('prop_type', ''),
                        name=row.get('name', ''),
                        scenario=row.get('scenario', ''),
                        signals=row.get('signals', ''),
                    )
                )
    except Exception as exc:
        print(f'[WARN] Could not parse {csv_path}: {exc}', file=sys.stderr)
    return props


def _ingest_fpv_dir(
    fpv_dir: Path,
    model_tag: str,
    results: dict[str, 'ModuleResult'],
) -> None:
    """Load one fpv_cva6 dir into results dict. Skips if no results_summary.csv."""
    parent_name = fpv_dir.parent.name  # e.g. "blackbox_load_unit"
    parts = parent_name.split('_', 1)
    mode = parts[0] if len(parts) == 2 else 'unknown'
    module = parts[1] if len(parts) == 2 else parent_name

    summary: dict[str, int] = {}
    csv_path = fpv_dir / 'results_summary.csv'
    if csv_path.exists():
        for line in csv_path.read_text().splitlines()[1:]:
            row_parts = line.strip().split(',')
            if len(row_parts) >= 2:
                try:
                    summary[row_parts[0]] = int(row_parts[1])
                except ValueError:
                    pass

    if not summary:
        return  # skip dirs without results

    jasper_status = _load_jasper_status(fpv_dir)
    props = _load_spec_csv(fpv_dir, module)
    for p in props:
        if p.name in jasper_status:
            p.status, p.cex_cycles = jasper_status[p.name]

    # Key: model_tag + mode + module — prefer higher-quality run if duplicate
    key = f'{model_tag}_{mode}_{module}' if model_tag else f'{mode}_{module}'
    if key not in results:
        results[key] = ModuleResult(
            module=module,
            mode=mode,
            model_tag=model_tag,
            fpv_dir=fpv_dir,
            summary=summary,
            properties=props,
        )


def load_fpv_results(
    base_dir: Path,
    model: Optional[str] = None,
    scan_all: bool = False,
) -> dict[str, 'ModuleResult']:
    """
    Scan for FPV results and return {key: ModuleResult}.

    Modes:
      scan_all=True  — recursive glob '**/ fpv_cva6', finds ALL model runs
      model=<tag>    — scan base_dir/<model>/*/fpv_cva6 only
      default        — scan base_dir/*/fpv_cva6 (gpt-5.1 / legacy results)
    """
    results: dict[str, ModuleResult] = {}

    if scan_all:
        # Recursive scan: find all fpv_cva6 dirs at any depth
        for fpv_dir in base_dir.glob('**/fpv_cva6'):
            if not fpv_dir.is_dir():
                continue
            # Derive model tag from grandparent dir if it's not a mode_module dir
            grandparent = fpv_dir.parent.parent
            model_tag = grandparent.name if grandparent != base_dir else ''
            # If grandparent is base_dir, it's a legacy (gpt-5.1) run
            if model_tag in ('', 'fpv_cva6'):
                model_tag = 'gpt51'
            _ingest_fpv_dir(fpv_dir, model_tag, results)
    elif model:
        scan_root = base_dir / model
        for fpv_dir in scan_root.glob('*/fpv_cva6'):
            _ingest_fpv_dir(fpv_dir, model, results)
        if not results:
            # Fallback: maybe model dirs are at base level
            for fpv_dir in base_dir.glob('*/fpv_cva6'):
                _ingest_fpv_dir(fpv_dir, model, results)
    else:
        for fpv_dir in base_dir.glob('*/fpv_cva6'):
            _ingest_fpv_dir(fpv_dir, 'gpt51', results)

    return results


# ── Bug classification ────────────────────────────────────────────────────────


def _score_property(bug_kw: set[str], prop: PropertyDetail) -> tuple[int, list[str]]:
    """Score how relevant a property is to a bug. Returns (score, overlap_kw)."""
    name_kw = extract_keywords(prop.name.replace('_', ' '))
    scenario_kw = extract_keywords(prop.scenario)
    signals_kw = extract_keywords(prop.signals.replace(',', ' ').replace('_', ' '))

    name_overlap = bug_kw & name_kw
    scenario_overlap = bug_kw & scenario_kw
    signals_overlap = bug_kw & signals_kw

    score = len(name_overlap) * 3 + len(scenario_overlap) * 2 + len(signals_overlap)
    all_overlap = sorted(name_overlap | scenario_overlap | signals_overlap)
    return score, all_overlap


def _responsible_modules(bug_kw: set[str]) -> list[str]:
    """Return modules whose responsibility keywords overlap with bug keywords."""
    matched: list[tuple[int, str]] = []
    for mod, kw_list in MODULE_RESPONSIBILITIES.items():
        overlap = bug_kw & set(kw_list)
        if overlap:
            matched.append((len(overlap), mod))
    matched.sort(reverse=True)
    return [m for _, m in matched]


def classify_bug(
    issue: dict,
    fpv_data: dict[str, ModuleResult],
) -> BugCoverage:
    title = issue.get('title', '')
    body = issue.get('body', '') or ''
    bug_kw = extract_keywords(f'{title} {body[:3000]}')

    resp_modules = _responsible_modules(bug_kw)
    tested_modules = {r.module for r in fpv_data.values()}

    # Gather all candidate properties across tested responsible modules
    all_matches: list[BugMatch] = []
    for key, result in fpv_data.items():
        if result.module not in resp_modules:
            continue
        for prop in result.properties:
            score, overlap = _score_property(bug_kw, prop)
            if score >= 2:
                all_matches.append(
                    BugMatch(
                        module=result.module,
                        mode=result.mode,
                        model_tag=result.model_tag,
                        property_name=prop.name,
                        status=prop.status,
                        score=score,
                        overlap_kw=overlap,
                    )
                )

    all_matches.sort(key=lambda m: (-m.score, m.property_name))
    top_matches = all_matches[:10]

    # Determine classification
    classification = NOT_APPLICABLE
    tested_resp = [m for m in resp_modules if m in tested_modules]
    untested_resp = [m for m in resp_modules if m not in tested_modules and m not in _UNTESTED_MODULES]
    known_untested_resp = [m for m in resp_modules if m in _UNTESTED_MODULES]

    if resp_modules:
        fail_matches = [m for m in top_matches if m.status == 'FAIL']
        proven_matches = [m for m in top_matches if m.status == 'PROVEN']

        if fail_matches:
            classification = DETECTED
        elif proven_matches:
            classification = POSSIBLY_COVERED
        elif tested_resp:
            classification = PROPERTY_GAP
        elif known_untested_resp or untested_resp:
            classification = MODULE_NOT_TESTED
        else:
            classification = NOT_APPLICABLE

    return BugCoverage(
        issue_number=issue.get('number', 0),
        title=title,
        url=issue.get('html_url', ''),
        classification=classification,
        responsible_modules=resp_modules,
        tested_modules=sorted(tested_resp),
        top_matches=top_matches,
        issue_keywords=sorted(bug_kw)[:15],
    )


# ── Reporting ─────────────────────────────────────────────────────────────────

_CLASS_ICON = {
    DETECTED: '🔴 DETECTED',
    POSSIBLY_COVERED: '🟡 POSSIBLY_COVERED',
    PROPERTY_GAP: '🟠 PROPERTY_GAP',
    MODULE_NOT_TESTED: '⚪ MODULE_NOT_TESTED',
    NOT_APPLICABLE: '⬜ NOT_APPLICABLE',
}

_CLASS_COLOR = {
    DETECTED: '#ffe0e0',
    POSSIBLY_COVERED: '#fff9c4',
    PROPERTY_GAP: '#ffe0b2',
    MODULE_NOT_TESTED: '#f0f0f0',
    NOT_APPLICABLE: '#fafafa',
}

_CLASS_BADGE = {
    DETECTED: 'background:#e53935;color:white',
    POSSIBLY_COVERED: 'background:#f9a825;color:black',
    PROPERTY_GAP: 'background:#ef6c00;color:white',
    MODULE_NOT_TESTED: 'background:#78909c;color:white',
    NOT_APPLICABLE: 'background:#bdbdbd;color:black',
}


def print_report(coverages: list[BugCoverage], fpv_data: dict[str, ModuleResult]) -> None:
    sep = '=' * 90
    total_props = sum(sum(r.summary.values()) for r in fpv_data.values())
    print(sep)
    print('  CVA6 GITHUB BUG DETECTION REPORT')
    print(sep)
    print(f'  Issues analyzed  : {len(coverages)}')
    print(f'  FPV modules      : {len(fpv_data)}')
    print(f'  Total properties : {total_props}')
    print()

    # Summary counts
    class_counts: Counter = Counter(c.classification for c in coverages)
    for cls, icon in _CLASS_ICON.items():
        print(f'  {icon:<32} {class_counts.get(cls, 0):>4}')
    print()

    for cov in coverages:
        icon = _CLASS_ICON[cov.classification]
        labels_resp = ', '.join(cov.responsible_modules) or 'unknown'
        print(f'  #{cov.issue_number:<6} [{icon}]')
        print(f'           {cov.title}')
        print(f'           URL      : {cov.url}')
        print(f'           Modules  : {labels_resp}')
        print(f'           Keywords : {", ".join(cov.issue_keywords[:8])}')
        if cov.top_matches:
            print('           Top property matches:')
            for m in cov.top_matches[:3]:
                tag = f'[{m.model_tag}] ' if m.model_tag else ''
                print(
                    f'             [{m.status:>12s}] {tag}{m.mode}_{m.module}::{m.property_name}'
                    f'  (score={m.score}, kw: {", ".join(m.overlap_kw[:4])})'
                )
        print()

    print(sep)


def write_html_report(
    coverages: list[BugCoverage],
    fpv_data: dict[str, ModuleResult],
    html_path: Path,
    mutation_summaries: list[MutationSummary] | None = None,
) -> None:
    total_props = sum(sum(r.summary.values()) for r in fpv_data.values())
    class_counts: Counter = Counter(c.classification for c in coverages)

    summary_html = ' &nbsp;|&nbsp; '.join(
        f'<span style="{_CLASS_BADGE[cls]};padding:2px 6px;border-radius:3px">{cls}: {class_counts.get(cls, 0)}</span>'
        for cls in [DETECTED, POSSIBLY_COVERED, PROPERTY_GAP, MODULE_NOT_TESTED, NOT_APPLICABLE]
    )

    rows = []
    for cov in coverages:
        badge_style = _CLASS_BADGE[cov.classification]
        badge = f'<span style="{badge_style};padding:2px 6px;border-radius:3px;font-size:0.8em">{cov.classification}</span>'

        props_html = ''
        if cov.top_matches:
            items = []
            for m in cov.top_matches[:5]:
                status_color = 'green' if m.status == 'PROVEN' else ('red' if m.status == 'FAIL' else '#888')
                tag_html = f'<small style="color:#607d8b">[{m.model_tag}]</small> ' if m.model_tag else ''
                items.append(
                    f'<li><code style="color:{status_color}">[{m.status}]</code> '
                    f'{tag_html}<small>{m.mode}_{m.module}</small>::<strong>{m.property_name}</strong>'
                    f' <small>(score={m.score})</small></li>'
                )
            props_html = "<ul style='margin:0;padding-left:1.2em'>" + ''.join(items) + '</ul>'
        else:
            props_html = '<em style="color:#999">no matching properties</em>'

        mods = ', '.join(f'<code>{m}</code>' for m in cov.responsible_modules[:3]) or '<em>unknown</em>'
        rows.append(
            f"""<tr style="background:{_CLASS_COLOR[cov.classification]}">
              <td><a href="{cov.url}" target="_blank">#{cov.issue_number}</a></td>
              <td>{cov.title}</td>
              <td>{badge}</td>
              <td>{mods}</td>
              <td>{props_html}</td>
            </tr>"""
        )

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>CVA6 Bug Detection Report</title>
<style>
  body {{ font-family: sans-serif; margin: 2em; font-size: 14px; }}
  h1 {{ color: #333; }}
  .summary {{ background:#f5f5f5; padding:1em; border-radius:4px; margin-bottom:1em; }}
  table {{ border-collapse:collapse; width:100%; }}
  th {{ background:#37474f; color:white; padding:8px; text-align:left; }}
  td {{ padding:8px; border-bottom:1px solid #ddd; vertical-align:top; }}
  tr:hover {{ filter: brightness(0.96); }}
  code {{ font-size:0.85em; }}
  ul {{ margin:0; padding-left:1.2em; }}
</style>
</head>
<body>
<h1>CVA6 Bug Detection Report — FPV Cross-Reference</h1>
<div class="summary">
  <strong>Issues:</strong> {len(coverages)} &nbsp;|&nbsp;
  <strong>FPV modules:</strong> {len(fpv_data)} &nbsp;|&nbsp;
  <strong>Total properties:</strong> {total_props}<br><br>
  {summary_html}
</div>
<table>
<thead>
  <tr><th>#</th><th>Issue Title</th><th>Classification</th><th>Modules</th><th>Matching FPV Properties</th></tr>
</thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
</body>
</html>"""
    mut_section = _mutation_html_section(mutation_summaries or [])
    html = html.replace('</body>', f'{mut_section}\n</body>')

    html_path.write_text(html, encoding='utf-8')
    print(f'[HTML] Report written to {html_path}')


# ── Mutation analysis ─────────────────────────────────────────────────────────


@dataclass
class MutationSummary:
    module: str
    total: int
    detected: int
    missed: int
    score_pct: float
    top_catching_props: list[tuple[str, int]]  # [(prop_name, catch_count), ...]
    details: list[dict]  # raw per-mutation dicts from mutation_test_fpv


def run_mutation_analysis(
    fpv_data: dict[str, ModuleResult],
    rtl_dir: Path,
    modules: list[str],
    jasper_bin: str,
    num_mutations: int,
    seed: int,
    timeout_s: int = 600,
) -> list[MutationSummary]:
    """
    Run random mutation testing for the requested modules using the existing
    mutation_test_fpv.run_mutation_test() and run_jasper_mutation() functions.
    Returns one MutationSummary per module tested.
    """
    from hagent.tool.mutation_test_fpv import run_mutation_test, print_module_report

    summaries: list[MutationSummary] = []

    for mod in modules:
        rtl_rel = MODULE_RTL_PATHS.get(mod)
        if not rtl_rel:
            print(f'[MUTATE] Unknown module "{mod}" — skipping', file=sys.stderr)
            continue

        rtl_file = rtl_dir / rtl_rel
        if not rtl_file.exists():
            print(f'[MUTATE] RTL file not found: {rtl_file} — skipping', file=sys.stderr)
            continue

        # Find the best fpv_dir for this module (prefer blackbox over whitebox)
        fpv_dir: Optional[Path] = None
        for key, result in fpv_data.items():
            if result.module == mod and result.mode == 'blackbox':
                fpv_dir = result.fpv_dir
                break
        if fpv_dir is None:
            for key, result in fpv_data.items():
                if result.module == mod:
                    fpv_dir = result.fpv_dir
                    break
        if fpv_dir is None:
            print(f'[MUTATE] No FPV dir found for module "{mod}" — skipping', file=sys.stderr)
            continue

        print(f'\n[MUTATE] === {mod} ===')
        print(f'         RTL : {rtl_file}')
        print(f'         FPV : {fpv_dir}')

        results = run_mutation_test(
            module_name=mod,
            rtl_file=rtl_file,
            fpv_dir=fpv_dir,
            jasper_bin=jasper_bin,
            num_mutations=num_mutations,
            seed=seed,
        )

        if not results:
            print(f'[MUTATE] No results for {mod}')
            continue

        report = print_module_report(mod, results)

        summaries.append(
            MutationSummary(
                module=mod,
                total=report['total_mutations'],
                detected=report['detected'],
                missed=report['missed'],
                score_pct=report['mutation_score_pct'],
                top_catching_props=sorted(report['property_hit_counts'].items(), key=lambda x: -x[1])[:8],
                details=report['mutations'],
            )
        )

    return summaries


def _mutation_html_section(summaries: list[MutationSummary]) -> str:
    """Generate an HTML section for mutation results to embed in the main report."""
    if not summaries:
        return ''

    rows = []
    for s in summaries:
        score_color = '#4caf50' if s.score_pct >= 70 else ('#ff9800' if s.score_pct >= 40 else '#f44336')
        score_badge = (
            f'<span style="background:{score_color};color:white;padding:2px 8px;'
            f'border-radius:3px;font-weight:bold">{s.score_pct:.1f}%</span>'
        )
        top_props = '<br>'.join(f'<code>[{cnt}x]</code> {p}' for p, cnt in s.top_catching_props[:5]) or '<em>none</em>'
        missed_ops = ', '.join(d['op'] for d in s.details if not d['detected'])[:120] or '—'
        rows.append(
            f'<tr>'
            f'<td><strong>{s.module}</strong></td>'
            f'<td style="text-align:center">{s.total}</td>'
            f'<td style="text-align:center;color:green">{s.detected}</td>'
            f'<td style="text-align:center;color:red">{s.missed}</td>'
            f'<td style="text-align:center">{score_badge}</td>'
            f'<td><small>{top_props}</small></td>'
            f'<td><small style="color:#888">{missed_ops}</small></td>'
            f'</tr>'
        )

    return f"""
<h2 style="margin-top:2em">🔬 Random Mutation Testing Results</h2>
<p style="color:#555">Random operator mutations injected into RTL; mutation score = % caught by FPV properties via Jasper CEX.</p>
<table style="border-collapse:collapse;width:100%">
<thead>
  <tr style="background:#37474f;color:white">
    <th style="padding:8px">Module</th>
    <th style="padding:8px">Mutations</th>
    <th style="padding:8px">Detected</th>
    <th style="padding:8px">Missed</th>
    <th style="padding:8px">Score</th>
    <th style="padding:8px">Top Catching Properties</th>
    <th style="padding:8px">Missed Operators</th>
  </tr>
</thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
"""


# ── CLI ───────────────────────────────────────────────────────────────────────


def main() -> None:
    parser = argparse.ArgumentParser(description='Fetch open CVA6 GitHub bug issues and cross-reference with FPV results')
    parser.add_argument('--owner', default='openhwgroup')
    parser.add_argument('--repo', default='cva6')
    parser.add_argument(
        '--out-dir',
        default=os.environ.get('HAGENT_BUILD_DIR', ''),
        help='FPV output base dir (default: $HAGENT_BUILD_DIR)',
    )
    parser.add_argument(
        '--model',
        default='',
        help='Model sub-directory tag (e.g. gpt53codex). Scans out-dir/model/',
    )
    parser.add_argument('--max-issues', type=int, default=100)
    parser.add_argument('--token', default=os.environ.get('GITHUB_TOKEN', ''))
    parser.add_argument('--label', default='Type:Bug')
    parser.add_argument(
        '--scan-all',
        action='store_true',
        help='Recursively scan ALL model subdirs (gpt51 + gpt53codex + ...) for combined coverage',
    )
    parser.add_argument('--out-json', help='Write enriched JSON')
    parser.add_argument('--html-out', help='Write HTML report')

    # ── Mutation testing args ──────────────────────────────────────────────────
    mut_grp = parser.add_argument_group('Mutation Testing (--mutate)')
    mut_grp.add_argument(
        '--mutate',
        action='store_true',
        help='Enable random mutation testing on top of GitHub cross-reference',
    )
    mut_grp.add_argument(
        '--rtl-dir',
        default=os.environ.get('CVA6_REPO_DIR', ''),
        help='CVA6 RTL core dir (default: $CVA6_REPO_DIR/core or $CVA6_REPO_DIR)',
    )
    mut_grp.add_argument(
        '--mutate-modules',
        default='',
        help='Comma-separated list of modules to mutate (default: all modules with FPV results)',
    )
    mut_grp.add_argument('--num-mutations', type=int, default=15, help='Random mutations per module (default: 15)')
    mut_grp.add_argument('--seed', type=int, default=42, help='Random seed for mutation selection (default: 42)')
    mut_grp.add_argument(
        '--jasper-bin',
        default=os.environ.get('JASPER_BIN', 'jg'),
        help='JasperGold binary path (default: $JASPER_BIN or "jg")',
    )
    mut_grp.add_argument('--mutate-timeout', type=int, default=600, help='Jasper timeout per mutation (s)')
    args = parser.parse_args()

    token = args.token or None

    out_dir = Path(args.out_dir) if args.out_dir else None
    if out_dir is None or not out_dir.is_dir():
        print(
            f"[WARN] --out-dir '{out_dir}' not found. Set $HAGENT_BUILD_DIR or pass --out-dir explicitly.",
            file=sys.stderr,
        )
        out_dir = None

    # 1. Fetch GitHub issues
    print(f"[1/3] Fetching open '{args.label}' issues from {args.owner}/{args.repo} ...")
    issues = fetch_open_issues(args.owner, args.repo, token, args.label, args.max_issues)
    if not issues:
        print('[ERROR] No issues fetched. Check --token or network access.', file=sys.stderr)
        sys.exit(1)
    print(f'       → {len(issues)} issues retrieved.')

    # 2. Load FPV results
    fpv_data: dict[str, ModuleResult] = {}
    if out_dir:
        model = args.model or None
        scan_all = args.scan_all
        if scan_all:
            print(f'[2/3] Loading FPV results (ALL models) from {out_dir} ...')
        else:
            print(f'[2/3] Loading FPV results from {out_dir}' + (f'/{model}' if model else '') + ' ...')
        fpv_data = load_fpv_results(out_dir, model, scan_all=scan_all)
        model_tags = sorted({r.model_tag for r in fpv_data.values()})
        total_props = sum(len(r.properties) for r in fpv_data.values())
        print(
            f'       → {len(fpv_data)} module runs loaded, {total_props} properties (models: {", ".join(model_tags) or "legacy"})'
        )
    else:
        print('[2/3] Skipping FPV load (no --out-dir).')

    # 3. Classify each bug
    print('[3/3] Classifying bugs against FPV coverage ...')
    coverages = [classify_bug(issue, fpv_data) for issue in issues]

    class_counts: Counter = Counter(c.classification for c in coverages)
    print(
        f'       → DETECTED={class_counts.get(DETECTED, 0)}, '
        f'POSSIBLY_COVERED={class_counts.get(POSSIBLY_COVERED, 0)}, '
        f'PROPERTY_GAP={class_counts.get(PROPERTY_GAP, 0)}, '
        f'MODULE_NOT_TESTED={class_counts.get(MODULE_NOT_TESTED, 0)}, '
        f'NOT_APPLICABLE={class_counts.get(NOT_APPLICABLE, 0)}'
    )

    print()
    print_report(coverages, fpv_data)

    # ── Optional: mutation testing ─────────────────────────────────────────────
    mutation_summaries: list[MutationSummary] = []
    if args.mutate:
        # Resolve RTL dir
        rtl_dir_raw = args.rtl_dir
        rtl_dir = Path(rtl_dir_raw) if rtl_dir_raw else None
        if rtl_dir and not rtl_dir.name == 'core':
            core_candidate = rtl_dir / 'core'
            if core_candidate.is_dir():
                rtl_dir = core_candidate
        if rtl_dir is None or not rtl_dir.is_dir():
            print(f'[MUTATE] --rtl-dir not found: {rtl_dir}. Set $CVA6_REPO_DIR.', file=sys.stderr)
        else:
            if args.mutate_modules:
                mut_modules = [m.strip() for m in args.mutate_modules.split(',') if m.strip()]
            else:
                # Default: all modules that have FPV results
                mut_modules = sorted({r.module for r in fpv_data.values()})

            print(f'\n[MUTATE] Testing {len(mut_modules)} modules: {", ".join(mut_modules)}')
            print(f'         RTL dir  : {rtl_dir}')
            print(f'         Mutations: {args.num_mutations} per module, seed={args.seed}')

            mutation_summaries = run_mutation_analysis(
                fpv_data=fpv_data,
                rtl_dir=rtl_dir,
                modules=mut_modules,
                jasper_bin=args.jasper_bin,
                num_mutations=args.num_mutations,
                seed=args.seed,
                timeout_s=args.mutate_timeout,
            )

            # Print mutation summary table
            if mutation_summaries:
                print()
                print('┌─── MUTATION TESTING SUMMARY ──────────────────────────────────────────┐')
                print(f'  {"Module":<18} {"Mutations":>9} {"Detected":>9} {"Missed":>7} {"Score%":>8}')
                print('  ' + '─' * 52)
                for s in mutation_summaries:
                    print(f'  {s.module:<18} {s.total:>9} {s.detected:>9} {s.missed:>7} {s.score_pct:>7.1f}%')
                print('└────────────────────────────────────────────────────────────────────────┘')

    if args.out_json:
        out_path = Path(args.out_json)
        serializable = []
        for cov in coverages:
            serializable.append(
                {
                    'number': cov.issue_number,
                    'title': cov.title,
                    'url': cov.url,
                    'classification': cov.classification,
                    'responsible_modules': cov.responsible_modules,
                    'tested_modules': cov.tested_modules,
                    'issue_keywords': cov.issue_keywords,
                    'top_matches': [
                        {
                            'module': m.module,
                            'mode': m.mode,
                            'model_tag': m.model_tag,
                            'property': m.property_name,
                            'status': m.status,
                            'score': m.score,
                            'overlap_keywords': m.overlap_kw,
                        }
                        for m in cov.top_matches
                    ],
                }
            )
        payload = {
            'github_bugs': serializable,
            'mutation_summaries': [
                {
                    'module': s.module,
                    'total_mutations': s.total,
                    'detected': s.detected,
                    'missed': s.missed,
                    'score_pct': s.score_pct,
                    'top_catching_props': s.top_catching_props,
                    'mutations': s.details,
                }
                for s in mutation_summaries
            ],
        }
        out_path.write_text(json.dumps(payload, indent=2))
        print(f'[JSON] Written to {out_path}')

    if args.html_out:
        write_html_report(coverages, fpv_data, Path(args.html_out), mutation_summaries)


if __name__ == '__main__':
    main()
