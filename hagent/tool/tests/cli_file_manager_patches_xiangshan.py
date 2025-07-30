#!/usr/bin/env python3
"""
File_manager test script that:
 1) Collects all .sv diffs.
 2) Saves them to YAML.
 3) Generates “hints” by:
    - Extracting keywords from each diff.
    - Restricting to the Scala files for that module.
    - Fuzzy‑searching those files for the keywords.
    - Clustering nearby matches into code blocks.
    - Slicing each block out with context.
 4) Saves the hints to xiangshan_hints.yaml for LLM prompting.
"""

import os
import sys
import pytest
from ruamel.yaml import YAML

from hagent.tool.file_manager import File_manager
from hagent.tool.fuzzy_grep import Fuzzy_grep
from hagent.tool.extract_verilog_diff_keywords import Extract_verilog_diff_keywords


def save_yaml(data, path):
    yaml = YAML()
    yaml.default_flow_style = False
    with open(path, 'w', encoding='utf-8') as f:
        yaml.dump(data, f)


def cluster_line_numbers(line_nums, max_gap=5):
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
        print(f"Setup failed: {fm.get_error()}"); sys.exit(1)

    # track & patch as before...
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
        print(f"Make failed: {fm.get_error()} code:{ec}"); sys.exit(7)

    patches = fm.get_patch_dict().get('patch', [])
    sv_patches = [p for p in patches if p['filename'].endswith('.sv')]
    save_yaml({'patch': sv_patches}, 'xiangshan_sv_patches.yaml')
    print(f"Saved {len(sv_patches)} SV diffs → xiangshan_sv_patches.yaml")

    # list all Scala files once (inside container)
    ec, files_txt, _ = fm.run(
        'find /code/XiangShan/src/main/scala/xiangshan -name "*.scala"',
        container_path='/'
    )
    scala_files = files_txt.splitlines()

    fg = Fuzzy_grep()
    fg.setup(language='chisel')

    hints = []
    for patch in sv_patches:
        diff = patch['diff']
        terms = Extract_verilog_diff_keywords.get_user_variables(diff)

        # skip empty
        if not terms:
            continue

        # derive module name (e.g. NewIFU.sv → NewIFU)
        base = os.path.splitext(os.path.basename(patch['filename']))[0].lower()

        # filter files whose basename contains module name
        module_files = [f for f in scala_files if base in os.path.basename(f).lower()]
        search_space = module_files or scala_files  # fallback if none

        # fuzzy‐grep each candidate file
        file_hits = {}
        for path in search_space:
            ec, content, _ = fm.run(f'cat {path}', container_path='/')
            if ec != 0:
                continue
            matches = fg.find_matches_in_text(content, terms, threshold=60)
            if matches:
                file_hits[path] = {
                    'lines': [ln for ln, _ in matches],
                    'content': content.splitlines()
                }

        # cluster & slice
        blocks = []
        for path, info in file_hits.items():
            clusters = cluster_line_numbers(info['lines'])
            for start, end in clusters:
                ctx_start = max(0, start - 5)
                ctx_end = min(len(info['content']), end + 6)
                snippet = "\n".join(
                    f"{i+1}: {info['content'][i]}"
                    for i in range(ctx_start, ctx_end)
                )
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

    save_yaml(hints, 'xiangshan_hints.yaml')
    print(f"Generated {len(hints)} hint entries → xiangshan_hints.yaml")


if __name__ == '__main__':
    main()
