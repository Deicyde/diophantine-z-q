# Every declaration of each draft: is a declaration of the same full name in the adopted modules,
# with the same whitespace-normalized block (statement and proof)? Prints the exceptions.
import sys, glob
sys.path.insert(0, 'scratch/hdec-adopt2'); sys.path.insert(0, 'scratch/hdec-adopt3')
from decls import decls
from blocks import norm
def blk(path, i):
    L = open(path).read().splitlines(keepends=True)
    j = i - 1; k = j + 1
    while k < len(L) and (L[k].startswith(' ') or (not L[k].strip() and k + 1 < len(L)
                          and L[k + 1].startswith(' '))): k += 1
    return norm(L[j:k])
PAIRS = [('scratch/glue-t32a/T32a.lean', ['ZInQKernel/HDecomp/B3Unram/B3b.lean',
                                           'ZInQKernel/HDecomp/B3Unram/T32a.lean'], 1816),
         ('scratch/leaf-modcurves/ModCurveLeaves.lean', glob.glob('ZInQKernel/HDecomp/ModCurves/*.lean'), 0),
         ('scratch/leaf-qm-fp/QMLeaves.lean', glob.glob('ZInQKernel/HDecomp/QM/*.lean'), 0),
         ('scratch/def-faltings/Faltings.lean', glob.glob('ZInQKernel/HDecomp/Faltings/*.lean'), 0)]
for draft, mods, skip in PAIRS:
    M = {}
    for f in mods:
        for n, p, i in decls(f): M[n] = (p, i)
    tot = same = 0
    for n, p, i in decls(draft):
        if i <= skip: continue
        tot += 1
        if n not in M: print('MISSING', draft.split('/')[-1], n); continue
        if blk(p, i) == blk(*M[n]): same += 1
        else: print('DIFFERS', draft.split('/')[-1], n)
    print(draft.split('/')[-1], f'{same}/{tot} identical')
