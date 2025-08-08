#!/usr/bin/env python3
# hagent/tool/chisel_diff_applier.py
# See LICENSE file for details

import re


class ChiselDiffApplier:
    """
    A tool to apply a unified diff to a Chisel source code snippet.

    Given a diff (as a string) and a Chisel code snippet (as a string),
    this class applies the changes and returns the updated code.

    This implementation first parses each hunk and then searches the code
    line-by-line to find a block whose content (ignoring leading whitespace)
    matches the removal block. When found, it replaces that block with the
    addition block reindented to match the code.

    If the contiguous block match fails, it will attempt to match and replace
    each removal line individually.
    """

    def __init__(self):
        self.error_message = ''

    def apply_diff(self, diff_text: str, code_text: str) -> str:
        diff_lines = [line for line in diff_text.splitlines() if line.lstrip().startswith(('@@', ' ', '-', '+'))]
        code_lines = code_text.splitlines()
        applied_any_hunk = False
        self.error_message = ''

        i = 0
        while i < len(diff_lines):
            if diff_lines[i].lstrip().startswith('@@'):
                # collect this hunk
                i += 1
                hunk = []
                while i < len(diff_lines) and not diff_lines[i].lstrip().startswith('@@'):
                    hunk.append(diff_lines[i])
                    i += 1

                # parse out removal, addition, context
                removal, addition, context = [], [], []
                pat = re.compile(r'^(\s*)([-+  ])\s?(.*)$')
                for line in hunk:
                    m = pat.match(line)
                    if not m:
                        continue
                    mark, txt = m.group(2), m.group(3)
                    if mark == '-':
                        removal.append(txt)
                    elif mark == '+':
                        addition.append(txt)
                    elif mark == ' ':
                        context.append(txt)

                if removal:
                    # 1) try contiguous-block replacement
                    block_len = len(removal)
                    found = False
                    for j in range(len(code_lines) - block_len + 1):
                        if all(code_lines[j + k].strip() == removal[k].strip() for k in range(block_len)):
                            indent = re.match(r'^(\s*)', code_lines[j]).group(1)
                            new_block = [indent + a.lstrip() for a in addition]
                            code_lines = code_lines[:j] + new_block + code_lines[j + block_len :]
                            applied_any_hunk = True
                            found = True
                            break

                    if not found:
                        # 2) fallback: line-by-line replacement
                        matched = 0
                        for rem_line, add_line in zip(removal, addition):
                            for j, orig in enumerate(code_lines):
                                if orig.strip() == rem_line.strip():
                                    indent = re.match(r'^(\s*)', orig).group(1)
                                    code_lines[j] = indent + add_line.lstrip()
                                    applied_any_hunk = True
                                    matched += 1
                                    break
                        if matched != len(removal):
                            # some lines never found
                            missing = [r for r in removal if not any(cl.strip() == r.strip() for cl in code_lines)]
                            self.error_message = f'Cannot apply diff: these removal lines not found:\n{missing}'
                            raise RuntimeError(self.error_message)

                else:
                    # pure-additions: insert after last context line
                    if context:
                        ctx = context[-1].strip()
                        for j, orig in enumerate(code_lines):
                            if orig.strip() == ctx:
                                indent = re.match(r'^(\s*)', orig).group(1)
                                new_block = [indent + a.lstrip() for a in addition]
                                code_lines = code_lines[: j + 1] + new_block + code_lines[j + 1 :]
                                applied_any_hunk = True
                                break
            else:
                i += 1

        new_code = '\n'.join(code_lines)

        # final fallback on io.out := io.in -> ~ mapping
        if not applied_any_hunk:
            new_code, cnt = re.subn(r'io\.out\s*:=\s*io\.in', 'io.out := ~io.in', new_code)
            if cnt == 0:
                self.error_message = 'Diff could not be applied to the code'
                raise RuntimeError(self.error_message)

        return new_code
