# Every declaration of each draft: is a declaration of the same full name in the adopted modules,
# with the same whitespace-normalized block (statement and proof)? Prints the exceptions.
import sys, glob
sys.path.insert(0, 'scratch/hdec-adopt2')
from decls import decls
from blocks import norm
def blk(path, i):
    L = open(path).read().splitlines(keepends=True)
    j = i - 1; k = j + 1
    while k < len(L) and (L[k].startswith(' ') or (not L[k].strip() and k + 1 < len(L)
                          and L[k + 1].startswith(' '))): k += 1
    return norm(L[j:k])
D = 'ZInQKernel/HDecomp/'
PAIRS = [('scratch/leaf-push2/LeafPush2.lean', glob.glob(D + 'LeafPush2/*.lean'), 'end ModelsSec'),
         ('scratch/bp-analytic/Torus.lean', glob.glob(D + 'Analytic/*.lean'), None),
         ('scratch/rv-qm-polar/QMPolar.lean', [D + 'QM/Polar.lean'], None)]
for draft, mods, skipto in PAIRS:
    skip = 0
    if skipto:
        skip = next(i for i, l in enumerate(open(draft), 1) if l.startswith(skipto))
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
    print(draft.split('/')[-1], f'{same}/{tot} identical (after line {skip})')
