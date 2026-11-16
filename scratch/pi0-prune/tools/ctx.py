#!/usr/bin/env python3
"""Print the namespace/section/open/variable context active at a line of a Lean file.
Usage: ctx.py FILE LINE"""
import sys, re
f, line = sys.argv[1], int(sys.argv[2])
lines = open(f).read().split('\n')
stack = []  # entries: [kind, name, [scoped commands]]
top = []
in_comment = 0
for i, l in enumerate(lines[:line-1], 1):
    s = l.strip()
    # crude block-comment tracking
    if in_comment:
        in_comment += s.count('/-') - s.count('-/')
        if in_comment <= 0: in_comment = 0
        continue
    if s.startswith('/-'):
        in_comment = s.count('/-') - s.count('-/')
        if in_comment <= 0: in_comment = 0
        continue
    m = re.match(r'^(noncomputable\s+)?(namespace|section)\b\s*(\S*)', l)
    if m:
        stack.append([m.group(2), m.group(3), [], i]); continue
    m = re.match(r'^end\b\s*(\S*)', l)
    if m:
        if stack: stack.pop()
        continue
    if re.match(r'^(open|variable|universe|set_option|local notation|notation|scoped|attribute|local instance|instance|local attribute|open scoped)\b', l):
        # gather continuation lines
        cmd = l
        j = i
        while j < len(lines) and lines[j].startswith('  ') and not re.match(r'^\s*(theorem|def|lemma)', lines[j]):
            cmd += '\n' + lines[j]; j += 1
        if re.match(r'^(set_option)', l) and ' in' in l.split('--')[0][-4:]:
            continue
        if re.match(r'^(instance|attribute)', l):
            cmd = '-- (ctx) ' + l
        (stack[-1][2] if stack else top).append((i, cmd))
for c in top: print(f'-- L{c[0]}\n{c[1]}')
for k, n, cmds, i in stack:
    print(f'{k} {n}  -- L{i}')
    for c in cmds: print(f'  -- L{c[0]}\n{c[1]}')
