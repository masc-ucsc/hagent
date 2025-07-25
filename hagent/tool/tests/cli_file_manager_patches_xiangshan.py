#!/usr/bin/env python3
"""
Enhanced File_manager test script that:
 1) Collects all .sv diffs.
 2) Saves them to YAML.
 3) Generates “hints” by:
    - Extracting keywords from each diff.
    - Fuzzy‑searching the Chisel tree *inside the Docker* for those keywords.
    - Clustering nearby matches into code blocks.
    - Slicing each block out with context.
 4) Saves the hints to xiangshan_hints.yaml for LLM prompting.
"""

import os
import sys
import pytest
from ruamel.yaml import YAML

# Make sure we can import our modules
sys.path.insert(0, '/Users/renau/projs/hagent')
script_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, script_dir)

from hagent.tool.file_manager import File_manager
from hagent.tool.fuzzy_grep import Fuzzy_grep
from hagent.tool.extract_verilog_diff_keywords import Extract_verilog_diff_keywords


def save_yaml(data, path):
    yaml = YAML()
    yaml.default_flow_style = False
    with open(path, 'w', encoding='utf-8') as f:
        yaml.dump(data, f)


def cluster_line_numbers(line_nums, max_gap=5):
    """
    Cluster sorted 0-based line numbers into contiguous regions where gaps <= max_gap.
    Returns list of (start, end).
    """
    if not line_nums:
        return []
    nums = sorted(set(line_nums))
    clusters = []
    start = prev = nums[0]
    for n in nums[1:]:
        if n - prev <= max_gap:
            prev = n
        else:
            clusters.append((start, prev))
            start = prev = n
    clusters.append((start, prev))
    return clusters


@pytest.mark.slow
def main():
    fm = File_manager('mascucsc/hagent-xiangshan:2025.07')
    if not fm.setup():
        print(f'Setup failed: {fm.get_error()}')
        sys.exit(2)

    # 1) Apply patch and run simulation (as before)...
    ifu = '/code/XiangShan/src/main/scala/xiangshan/frontend/IFU.scala'
    rtl = '/code/XiangShan/build/rtl'
    fm.track_file(ifu)
    fm.track_dir(rtl, ext='.sv')
    fm.apply_line_patch(
        ifu, 257,
        '  f2_flush         := backend_redirect || mmio_redirect || wb_redirect',
        '  f2_flush         := backend_redirect && mmio_redirect || wb_redirect'
    )
    ec, _, _ = fm.run('make CONFIG=MinimalConfig EMU_THREADS=1 sim-verilog',
                     container_path='/code/XiangShan')
    if ec != 0:
        print(f'Make failed: {fm.get_error()} code:{ec}')
        sys.exit(7)

    patches = fm.get_patch_dict().get('patch', [])
    sv_patches = [p for p in patches if p['filename'].endswith('.sv')]
    save_yaml({'patch': sv_patches}, 'xiangshan_sv_patches.yaml')
    print(f"Saved {len(sv_patches)} SV diffs")

    # 2) Prepare Fuzzy_grep
    fg = Fuzzy_grep()
    fg.setup(language='chisel')

    # 3) Get list of Scala files *inside* the container
    ec, files_txt, _ = fm.run(
        'find /code/XiangShan/src/main/scala/xiangshan -name "*.scala"',
        container_path='/'
    )
    scala_files = files_txt.splitlines()

    hints = []
    for patch in sv_patches:
        diff = patch['diff']
        terms = Extract_verilog_diff_keywords.get_user_variables(diff)

        # 4) For each Scala file in container, cat & fuzzy‐grep
        file_matches = {}
        for path in scala_files:
            ec, content, _ = fm.run(f'cat {path}', container_path='/')
            if ec != 0:
                continue
            matches = fg.find_matches_in_text(content, terms, threshold=60)
            if matches:
                file_matches[path] = {
                    'content': content.splitlines(),
                    'matches': matches
                }

        # 5) Cluster matches into blocks and slice context
        blocks = []
        for path, info in file_matches.items():
            lines = info['content']
            nums = [ln for ln, _ in info['matches']]
            for start, end in cluster_line_numbers(nums):
                ctx_start = max(0, start - 5)
                ctx_end = min(len(lines), end + 6)
                snippet = "\n".join(f"{i+1}: {lines[i]}" for i in range(ctx_start, ctx_end))
                blocks.append({
                    'scala_file': path,
                    'lines': f"{ctx_start+1}-{ctx_end}",
                    'context': snippet
                })

        hints.append({
            'sv_file': patch['filename'],
            'diff_snippet': "\n".join(diff.splitlines()[:3]) + "...",
            'search_terms': terms,
            'chisel_hints': blocks
        })

    # 6) Save hints for LLM
    save_yaml(hints, 'xiangshan_hints.yaml')
    print(f"Generated {len(hints)} hint entries → xiangshan_hints.yaml")


if __name__ == '__main__':
    main()
