#!/usr/bin/env python3
"""parts/b10_abvarbc.lean: ZInQKernel/Contrib/AbVarBC/{Dim,Points,Tate,Torsion,Mul,Tangent,KerUnit,G9Instance,
G9Mul,Main}.lean (task g9-abvarbc) in import order, minus imports and `#print` lines, each in its own section,
with the name edits that put it over Leaves.lean's objects inside `HDec` (the kernel's `HDecomp/Objects.lean`
and G9's I3/I4 layer are verbatim copies of Leaves.lean's `PkgI3`, `PkgI4`; a95 omits G9's layers):
  `_root_.PkgI3` -> `_root_.HDec.PkgI3`;  `ZInQ.Contrib.G9.PkgI3.AbVar` -> `_root_.HDec.PkgI3.AbVar`;
  `ZInQ.Contrib.G9.PkgI4.I3.AbVar` -> `_root_.HDec.PkgI4.I3.AbVar`;
  `ZInQ.Contrib.G9.G0Galois.G9Glue` -> `_root_.HDec.G0Galois.G9Glue`.
An unclosed `noncomputable section` gets its `end`."""
import re
files = ['Dim','Points','Tate','Torsion','Mul','Tangent','KerUnit','G9Instance','G9Mul','Main']
rep = [('ZInQ.Contrib.G9.PkgI3.AbVar', '_root_.HDec.PkgI3.AbVar'),
       ('ZInQ.Contrib.G9.PkgI4.I3.AbVar', '_root_.HDec.PkgI4.I3.AbVar'),
       ('ZInQ.Contrib.G9.G0Galois.G9Glue', '_root_.HDec.G0Galois.G9Glue'),
       ('_root_.PkgI3', '_root_.HDec.PkgI3')]
out = ['/-! ## leaf-fold2: g9-abvarbc (ZInQKernel/Contrib/AbVarBC/*.lean), copied; see mk_abvarbc.py -/', '']
for f in files:
    s = open('../../ZInQKernel/Contrib/AbVarBC/%s.lean' % f).read()
    for a, b in rep: s = s.replace(a, b)
    lines = [l for l in s.split('\n') if not l.startswith('import ') and not l.startswith('#print')]
    s = '\n'.join(lines)
    if re.search(r'^noncomputable section\s*$', s, re.M) and not re.search(r'^end\s*$', s, re.M):
        s += '\nend\n'
    out += ['-- ===== ZInQKernel/Contrib/AbVarBC/%s.lean' % f, 'section LF2_AbVarBC_%s' % f, s, 'end LF2_AbVarBC_%s' % f, '']
open('parts/b10_abvarbc.lean', 'w').write('\n'.join(out))
