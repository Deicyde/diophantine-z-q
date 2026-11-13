# For each top-level declaration of the drafts, find HDecomp declarations with the same last name
# component and compare whitespace-normalized blocks (identical / differs).
import sys, glob, re
sys.path.insert(0, 'scratch/hdec-adopt2')
from decls import decls
from blocks import block, norm
hd = glob.glob('ZInQKernel/HDecomp/**/*.lean', recursive=True)
H = {}
for f in hd:
    for n, p, i in decls(f): H.setdefault(n.split('.')[-1], []).append((n, p, i))
def blk(path, i):
    L = open(path).read().splitlines(keepends=True)
    j = i - 1; s = j
    if s > 0 and L[s - 1].rstrip().endswith('-/'):
        s -= 1
        while not L[s].lstrip().startswith('/-'): s -= 1
    k = j + 1
    while k < len(L) and (L[k].startswith(' ') or (not L[k].strip() and k + 1 < len(L) and L[k+1].startswith(' '))): k += 1
    code = [l for l in L[j:k]]
    return norm(code)
for f in sys.argv[1:]:
    for n, p, i in decls(f):
        s = n.split('.')[-1]
        for hn, hp, hi in H.get(s, []):
            same = blk(p, i) == blk(hp, hi)
            print(('SAME ' if same else 'diff ') + n, '~', hn, hp.split('HDecomp/')[1] + ':' + str(hi), f.split('/')[-1] + ':' + str(i))
