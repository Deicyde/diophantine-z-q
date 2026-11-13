#!/usr/bin/env python3
"""Classify every vendored file under ZInQKernel/Contrib/TauCeti against its Tau Ceti source.

For each file with a provenance line `-- Vendored from Tau Ceti (..., commit SHA, module M)`,
regenerate the tcport.py output from the checkout of that commit (~/tc-oct16 or ~/tc-nov01) and
compare byte for byte. Prints: identical / modified (with diff line counts) / no-provenance.
Usage: python3 regen_diff.py WORKTREE
"""
import os, re, sys, difflib
root = sys.argv[1]
T = os.path.join(root, 'ZInQKernel', 'Contrib', 'TauCeti')
srcs = {'5a01f5fe3621': os.path.expanduser('~/tc-oct16'), '97a5b23586f9': os.path.expanduser('~/tc-nov01')}
pat = re.compile(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)TauCeti\.', re.M)
prov = re.compile(r'^-- Vendored from Tau Ceti \(https://github.com/TauCetiProject/TauCeti, commit ([0-9a-f]{12}), module ([\w.]+)\), Apache-2.0.$', re.M)
ident, modif, noprov = [], [], []
for dp, _, fs in os.walk(T):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); rel = os.path.relpath(p, T)
        txt = open(p, encoding='utf-8').read()
        m = prov.search(txt)
        if not m: noprov.append(rel); continue
        sha, mod = m.groups()
        s = os.path.join(srcs[sha], *mod.split('.')) + '.lean'
        o = open(s, encoding='utf-8').read()
        o = pat.sub(r'\1ZInQKernel.Contrib.TauCeti.', o)
        i = o.find('-/\n')
        o = o[:i+3] + m.group(0) + '\n' + o[i+3:] if i >= 0 else m.group(0) + '\n' + o
        expected_path = os.path.join(*mod.split('.')[1:]) + '.lean'
        if o == txt and expected_path == rel:
            ident.append(rel)
        else:
            d = list(difflib.unified_diff(o.splitlines(), txt.splitlines(), lineterm='', n=0))
            add = sum(1 for l in d if l.startswith('+') and not l.startswith('+++'))
            rem = sum(1 for l in d if l.startswith('-') and not l.startswith('---'))
            modif.append((rel, sha, mod, add, rem, expected_path == rel))
print(f'identical: {len(ident)}  modified: {len(modif)}  no provenance line: {len(noprov)}')
for r in sorted(modif): print('MODIFIED', r[0], r[1], r[2], f'+{r[3]} -{r[4]}', '' if r[5] else 'PATH-DIFFERS-FROM-MODULE')
for r in sorted(noprov): print('NOPROV', r)
