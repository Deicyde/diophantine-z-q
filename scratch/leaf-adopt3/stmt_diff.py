#!/usr/bin/env python3
"""leaf-adopt3: compare every declaration of the base Leaves.lean (883c4ddf) with the new one.
Declarations are keyed by namespace + name; for theorems the statement (text before `:=`) is
compared, for defs/structures/classes/abbrevs/opaques the whole declaration text without
comments. Prints changed, removed, added (counts and names)."""
import re, subprocess, sys
def decls(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)       # block comments and docstrings
    text = re.sub(r'--[^\n]*', '', text)
    ns = []
    out = {}
    cur = None
    kw = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|structure|class|opaque|instance|inductive)\s+([^\s:({\[]+)')
    for line in text.split('\n'):
        m_ns = re.match(r'^namespace\s+(\S+)', line)
        m_end = re.match(r'^end\s+(\S+)\s*$', line)
        if m_ns:
            ns.append(m_ns.group(1)); cur = None; continue
        if m_end and ns and m_end.group(1) == ns[-1]:
            ns.pop(); cur = None; continue
        m = kw.match(line)
        if m:
            name = m.group(2)
            full = name[6:] if name.startswith('_root_.') else '.'.join(ns + [name])
            cur = (m.group(1), full)
            out[cur] = [line]
            continue
        if line and not line[0].isspace() and not line.startswith(')'):
            cur = None  # a new top-level command
        if cur is not None:
            out[cur].append(line)
    res = {}
    for (k, n), lines in out.items():
        body = ' '.join(' '.join(lines).split())
        if k in ('theorem', 'lemma', 'instance'):
            body = body.split(':=')[0]
        res[n] = (k, body)
    return res
base = subprocess.run(['git', 'show', '883c4ddf:scratch/h-decomposition/Leaves.lean'],
                      capture_output=True, text=True, check=True).stdout
new = open(sys.argv[1] if len(sys.argv) > 1 else 'scratch/h-decomposition/Leaves.lean').read()
B, N = decls(base), decls(new)
changed = [n for n in B if n in N and B[n] != N[n]]
removed = [n for n in B if n not in N]
added = [n for n in N if n not in B]
print(f'base decls {len(B)}, new decls {len(N)}; changed {len(changed)}, removed {len(removed)}, added {len(added)}')
print('CHANGED:'); [print('  ', n) for n in changed]
print('REMOVED:'); [print('  ', n) for n in removed]
print('ADDED (namespaces):')
from collections import Counter
c = Counter(n.rsplit('.', 1)[0] if '.' in n else '<root>' for n in added)
for k, v in sorted(c.items()): print(f'   {k}: {v}')
