#!/usr/bin/env python3
"""Regenerate the selmer-2infty backport from Tau Ceti main 0642eae2 (S: supplemented modules, W: whole new
modules), under ZInQKernel/Contrib/TauCeti/Backport/Main0642/."""
import json, os, subprocess, sys

L = os.environ['TAUCETI_MAIN']  # a checkout of Tau Ceti at commit 0642eae29e0a59ef798d04de325386445906e755
T5 = os.environ['TAUCETI_5A01']  # a clone of Tau Ceti containing commit 5a01f5fe
Z = os.environ.get('REPO', '.')  # this repository
R5 = '5a01f5fe3621126cccf9ba22e700493cbc7b7156'
STATE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'state.json')
VD = 'ZInQKernel/Contrib/TauCeti/'
BD = 'ZInQKernel/Contrib/TauCeti/Backport/'
MD = 'ZInQKernel/Contrib/TauCeti/Backport/Main0642/'

st = json.load(open(STATE)) if os.path.exists(STATE) else {'S': [], 'W': []}
st.setdefault('O', {})
st.setdefault('P', {})
st.setdefault('X', {})
for a in sys.argv[1:]:
    k, p = a.split(':', 1)
    if k == 'X':
        vf, nm = p.split('=', 1)
        st['X'].setdefault(vf, [])
        if nm not in st['X'][vf]:
            st['X'][vf].append(nm)
        continue
    if k == 'O':
        path, olds = p.split('=', 1)
        st['O'][path] = olds.split(',')
        if path not in st['S']:
            st['S'].append(path)
        continue
    if p not in st[k]:
        st[k].append(p)
json.dump(st, open(STATE, 'w'), indent=1)

files5 = set(subprocess.run(['git', '-C', T5, 'ls-tree', '-r', '--name-only', R5], capture_output=True,
                            text=True).stdout.split())


def equiv5(p):
    if p in files5:
        return p
    if p.endswith('/Basic.lean'):
        q = p[:-len('/Basic.lean')] + '.lean'
        if q in files5:
            return q
    return None


allfiles = [f for f in subprocess.run(['git', '-C', L, 'ls-files', 'TauCeti'], capture_output=True,
                                      text=True).stdout.split() if f.endswith('.lean')]
S, W = set(st['S']), set(st['W'])
M = {}
for p in allfiles:
    name = p[:-5].replace('/', '.')
    rel = p[len('TauCeti/'):-5]
    if p in S or p in W:
        M[name] = 'ZInQKernel.Contrib.TauCeti.Backport.Main0642.' + rel.replace('/', '.')
        continue
    e = equiv5(p)
    if e and not os.path.exists(os.path.join(Z, VD + e[len('TauCeti/'):])) and \
            os.path.exists(os.path.join(Z, BD + e[len('TauCeti/'):])):
        # not vendored at 5a01f5fe, but an earlier task backported the whole module
        M[name] = 'ZInQKernel.Contrib.TauCeti.Backport.' + e[len('TauCeti/'):-5].replace('/', '.')
    elif e:
        M[name] = 'ZInQKernel.Contrib.TauCeti.' + e[len('TauCeti/'):-5].replace('/', '.')
    else:
        M[name] = 'ZInQKernel.Contrib.TauCeti.Backport.Main0642.' + rel.replace('/', '.')
json.dump(M, open(os.environ.get('BP_IMPORTMAP', 'importmap.json'), 'w'))

import re as _re
_imp_cache = {}
def latest_imports(p):
    if p not in _imp_cache:
        try:
            t = open(os.path.join(L, p), encoding='utf-8').read()
        except FileNotFoundError:
            t = ''
        _imp_cache[p] = [m.replace('.', '/') + '.lean' for m in
                         _re.findall(r'^(?:public |private )?(?:meta )?import (TauCeti\.[\w.]+)', t, _re.M)]
    return _imp_cache[p]
def closure(p):
    seen, stack = set(), [p]
    while stack:
        q = stack.pop()
        if q in seen:
            continue
        seen.add(q)
        stack.extend(latest_imports(q))
    seen.discard(p)
    return seen
# expose definitions of vendored modules whose bodies the backported proofs unfold
for vf, nms in st['X'].items():
    f = os.path.join(Z, vf)
    t = open(f, encoding='utf-8').read().split('\n')
    changed = False
    for nm in nms:
        for i, l in enumerate(t):
            if _re.match(r'^(?:noncomputable\s+)?def\s+' + _re.escape(nm) + r'\b', l):
                if i > 0 and t[i - 1].strip() == '@[expose]':
                    break
                t.insert(i, '@[expose]')
                changed = True
                break
        else:
            print('EXPOSE TARGET NOT FOUND', vf, nm)
    note = ('-- Modified for the Z-in-Q kernel: `@[expose]` added to definitions whose bodies the Backport/Main0642 '
            'modules unfold (task selmer-2infty): ')
    t = [l for l in t if not l.startswith(note)]
    idx = next(i for i, l in enumerate(t) if l.startswith('-- Vendored from Tau Ceti'))
    t.insert(idx + 1, note + ', '.join('`' + n + '`' for n in nms) + '.')
    open(f, 'w', encoding='utf-8').write('\n'.join(t))
unvendored = []
for p in sorted(S | W):
    rel = p[len('TauCeti/'):]
    out = MD + rel
    if p in W:
        olds = 'NONE'
    elif p in st['O']:
        olds = ','.join(st['O'][p])
    else:
        e = equiv5(p)
        erel = e[len('TauCeti/'):]
        olds = [VD + erel]
        if not os.path.exists(os.path.join(Z, VD + erel)):
            unvendored.append(e)
        if os.path.exists(os.path.join(Z, BD + erel)):
            olds.append(BD + erel)
        olds = ','.join(olds)
    r = subprocess.run(['python3', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bp_supplement.py'), p, olds, out, '--force'], capture_output=True, text=True)
    print(r.stdout.strip()[:300], r.stderr.strip()[:300])
    # make every supplemented module of the latest import closure visible
    extra = sorted(q for q in closure(p) & (S | W))
    if extra:
        f = os.path.join(Z, out)
        t = open(f, encoding='utf-8').read().split('\n')
        idx = max(i for i, l in enumerate(t) if _re.match(r'^\s*(public\s+)?(meta\s+)?import\s', l))
        have = set(l.strip() for l in t)
        add = ['public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.' + q[len('TauCeti/'):-5].replace('/', '.')
               for q in extra]
        add = [x for x in add if x not in have]
        t = t[:idx + 1] + add + t[idx + 1:]
        open(f, 'w', encoding='utf-8').write('\n'.join(t))
    for a, b in st['P'].get(p, []):
        f = os.path.join(Z, out)
        t = open(f, encoding='utf-8').read()
        n = t.count(a)
        if n != 1:
            print('PATCH FAILED', p, n, a[:80])
            continue
        t = t.replace(a, b)
        open(f, 'w', encoding='utf-8').write(t)
    if st['P'].get(p):
        print('   patched', len(st['P'][p]))
print('UNVENDORED 5a01 equivalents:', unvendored)

# report imports that do not resolve to files
missing_vendor, missing_bp = set(), set()
for p in sorted(S | W):
    f = os.path.join(Z, MD + p[len('TauCeti/'):])
    for m in _re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(ZInQKernel\.Contrib\.TauCeti\.[\w.]+)',
                         open(f, encoding='utf-8').read(), _re.M):
        path = m.replace('.', '/') + '.lean'
        if os.path.exists(os.path.join(Z, path)):
            continue
        if m.startswith('ZInQKernel.Contrib.TauCeti.Backport.Main0642.'):
            missing_bp.add('TauCeti/' + m[len('ZInQKernel.Contrib.TauCeti.Backport.Main0642.'):].replace('.', '/') + '.lean')
        else:
            missing_vendor.add('TauCeti.' + m[len('ZInQKernel.Contrib.TauCeti.'):])
print('MISSING-VENDOR (5a01 modules to vendor):', sorted(missing_vendor))
print('MISSING-BP (new latest modules to add as W):', sorted(missing_bp))
