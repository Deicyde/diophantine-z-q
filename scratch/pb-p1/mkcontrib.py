"""Write ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean from scratch/pb-p1/FontaineSt.lean.txt (drop #print lines,
add the provenance line). Run from the repository root: python3 scratch/pb-p1/mkcontrib.py"""
src = open('scratch/pb-p1/FontaineSt.lean.txt').read().split('\n')
out = [l for l in src if not l.startswith('#print')]
while out and out[-1] == '':
    out.pop()
s = '\n'.join(out) + '\n'
s = s.replace('# pb-p1: Fontaine', 'Copyright: this file is part of the fork Deicyde/diophantine-z-q (task pb-p1, 2026-11-17). Report\n'
              '`docs/research/pb-p1.md`; generated from `scratch/pb-p1/FontaineSt.lean.txt` by `scratch/pb-p1/mkcontrib.py`.\n\n'
              '# pb-p1: Fontaine', 1)
open('ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean', 'w').write(s)
