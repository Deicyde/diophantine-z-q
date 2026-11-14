#!/usr/bin/env python3
"""parts/a75_kernelfield.lean: g0-assemble2's part a75 with its copy of kernel-field's New.lean (from
`# Part 6`) replaced by the current scratch/kernel-field/New.lean (task kernel-field's later commits
8a8d29bf, 3106cab5: `oMaximal` proved, `EndTransport` from `EndTransportBC`, `EndTransportBC` from
`RigidityHom`), with g0-assemble2's three edits re-applied: `open GlueB3Unram hiding UnramifiedAt`;
the section FS5Copy (part 40 defines `G0FibreSimple.FibreComTrivial`) dropped; bare `open ZInQ`
also opens the kernel's root `ZInQ` (HDec wrapper)."""
import re
old = open('../g0-assemble2/parts/a75_kernelfield.lean').read().split('\n')
S = next(i for i, l in enumerate(old) if 'Part 6 (new, task kernel-field)' in l)
new = open('../kernel-field/New.lean').read()
new = new.replace('open GlueB3Unram GlueDescent.B2Q NumberField PkgI3 PkgI3.AbVar CategoryTheory MonObj',
                  'open GlueB3Unram hiding UnramifiedAt\nopen GlueDescent.B2Q NumberField PkgI3 PkgI3.AbVar CategoryTheory MonObj')
a = new.index('section FS5Copy'); b = new.index('end FS5Copy') + len('end FS5Copy')
new = new[:a] + "-- (g0-assemble2) section FS5Copy (verbatim copy of g0-fibresimple's `FibreComTrivial`) is not repeated: part 40 defines it." + new[b:]
out = []
for l in ('\n'.join(old[:S]) + '\n' + new).split('\n'):
    if l.startswith('open ') and re.search(r'(?<![\w.])ZInQ(?=\s|$)', l):
        l = re.sub(r'(?<![\w.])ZInQ(?=\s|$)', '_root_.ZInQ ZInQ', l, count=1)
    l = l.replace('_root_.PkgI4', '_root_.HDec.PkgI4')
    out.append(l)
open('parts/a75_kernelfield.lean', 'w').write('-- (leaf-fold2: g0-assemble2 part a75 with kernel-field New.lean updated; see mk_a75.py)\n' + '\n'.join(out))
