#!/usr/bin/env python3
"""Copy g0-assemble2's parts into parts/ with the two name-resolution edits the `HDec` wrapper needs
(leaf-fold §1): `_root_.PkgI4` -> `_root_.HDec.PkgI4` (Leaves.lean's PkgI4 now lives in HDec), and in
`open` lines a bare `ZInQ` also opens the kernel's root `ZInQ` (`open _root_.ZInQ ZInQ ...`)."""
import glob, os, re
os.makedirs('parts', exist_ok=True)
for p in sorted(glob.glob('../g0-assemble2/parts/*.lean')):
    s = open(p).read()
    n = 0
    s2 = s.replace('_root_.PkgI4', '_root_.HDec.PkgI4'); n += s.count('_root_.PkgI4')
    out = []
    for l in s2.split('\n'):
        if l.startswith('open ') and re.search(r'(?<![\w.])ZInQ(?=\s|$)', l):
            l = re.sub(r'(?<![\w.])ZInQ(?=\s|$)', '_root_.ZInQ ZInQ', l, count=1); n += 1
        out.append(l)
    s2 = '\n'.join(out)
    hdr = '-- (leaf-fold2: copied from scratch/g0-assemble2/parts/%s; %d HDec name-resolution edits)\n' % (os.path.basename(p), n)
    open('parts/' + os.path.basename(p), 'w').write(hdr + s2)
    if n: print(os.path.basename(p), n)
