#!/usr/bin/env python3
"""Verbatim check (task frobchain-contrib). Run from the repository root.

Each source slice used by build_modules.py (with `#print` lines dropped) must occur character for
character in its generated module; each Prop of the chain must be defined exactly once in
ZInQKernel/Contrib/FrobChain/ (or in frob-contrib's / frob-pieces' Contrib file), with the owner's
docstring + def text."""
import re

D = 'ZInQKernel/Contrib/FrobChain/'


def rd(p):
    return open(p).read()


def noprint(s):
    return '\n'.join(l for l in s.split('\n') if not l.startswith('#print'))


def L(p, a, b=None):
    ls = rd(p).split('\n')
    return '\n'.join(ls[a - 1:(b if b is not None else len(ls))])


red = rd('scratch/alg-frob-red/part_red.lean').split('\n')
checks = [
    ('TateBridge', noprint(L('scratch/unram-tate/TateBridge.lean', 17))),
    ('Bridge35', noprint(rd('scratch/g14-trace/part_bridge.lean'))),
    ('FrobTrace', noprint(rd('scratch/frob-trace/part_frob.lean'))),
    ('Rigidity', noprint(L('scratch/mul-rigidity/Rigidity.lean', 5))),
    ('AlgFrobRed', noprint('\n'.join(red[:1362]))),
    ('AlgFrobRed', noprint('\n'.join(red[1373:]))),
    ('FExtend', noprint(rd('scratch/afr-absfrob/part_fext.lean'))),
    ('LinkedStatement', L('scratch/g14-trace/part_g14.lean', 26, 30)),
    ('LinkedStatement', L('scratch/g14-trace/part_g14.lean', 146, 162)),
    ('LinkedStatement', L('scratch/linked-tate/parts/97_linkeddata.lean', 15, 25)),
    ('LinkedStatement', L('scratch/linked-tate/parts/97_linkeddata.lean', 125, 135)),
    ('LinkedStatement', L('scratch/linked-tate/parts/97_linkeddata.lean', 193, 233)),
    ('LinkedFrob', noprint(rd('scratch/linked-frob/parts/10_linkedfrob.lean'))),
    ('LinkedFrob', L('scratch/linked-frob/parts/20_bundle4.lean', 1, 37)),
]
for f in ['good', 'neron', 'final', 'full']:
    checks.append(('Pieces', noprint(rd('scratch/frob-pieces/part_%s.lean' % f))))

ok = True
for mod, txt in checks:
    r = txt.rstrip() in rd(D + mod + '.lean')  # the generator drops trailing blank lines
    ok &= r
    print(r, mod, len(txt.split('\n')), 'lines')

# the dropped `def AbsFrob` block is frob-contrib's text
r = '\n'.join(red[1362:1373]) in rd('ZInQKernel/Contrib/AbsFrob/AlgFrobRed.lean')
ok &= r
print(r, 'AbsFrob block (part_red 1363-1373) in Contrib/AbsFrob/AlgFrobRed.lean')

# each Prop of the chain is defined once over all Contrib files that the chain imports
allc = ''.join(rd(D + m + '.lean') for m in ['TateBridge', 'Bridge35', 'FrobTrace', 'Rigidity',
                                              'AlgFrobRed', 'FExtend', 'Pieces',
                                              'LinkedStatement', 'LinkedFrob', 'Main'])
allc += rd('ZInQKernel/Contrib/AbsFrob/AlgFrobRed.lean')
allc += rd('ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean')
for name in ['TateBridge35', 'FrobTraceLink', 'AlgFrobRed', 'AlgFrobOne', 'AlgFrobLink', 'LinkedFrob',
             'AbsFrob', 'FExtendGen', 'GoodRedCofinite', 'SmoothGeomConnIntegral', 'AbVarSpreadsOut',
             'ProperSmoothGenConnected', 'AbSchemeSpreadsOut', 'RigidityHom', 'G7Data', 'tmOf']:
    n = len(re.findall(r'^def %s\b' % name, allc, re.M))
    print(n, 'def', name)

print('ALL OK' if ok else 'FAILURE')
