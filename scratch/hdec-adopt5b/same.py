# Every declaration of each draft: is a declaration of the same full name in the adopted modules,
# with the same whitespace-normalized block (statement and proof)? A name missing there must be a
# verbatim copy of existing HDecomp code (scratch/hdec-adopt3/dups.py says SAME), which the module
# now imports. Prints the exceptions and a table. Usage: same.py T10SRC (as for adopt5b.py).
import sys, glob, subprocess
sys.path.insert(0, 'scratch/hdec-adopt2')
from decls import decls
from blocks import norm
def blk(path, i):
    L = open(path).read().splitlines(keepends=True)
    j = i - 1; k = j + 1
    while k < len(L) and (L[k].startswith(' ') or (not L[k].strip() and k + 1 < len(L)
                          and L[k + 1].startswith(' '))): k += 1
    return norm(L[j:k])
T = 'ZInQKernel/HDecomp/Textbook/'
M = {}
for f in glob.glob(T + '**/*.lean', recursive=True):
    for n, p, i in decls(f): M.setdefault(n, (p, i))
S = 'scratch/'
DR = [S + 't-different/All.lean'] + [S + 't-skolem-kw/' + f + '.lean' for f in
      'SkolemNoether BrauerNesbitt C10Closed FrobeniusDense KroneckerWeberUse '
      'ChebotarevCyclotomic'.split()] + [S + 't30-adelic/' + f + '.lean' for f in
      'SqrtCrit Adelic G1Count'.split()] + [sys.argv[1], S + 't28-igusa/Igusa.lean']
for d in DR:
    out = subprocess.run(['python3', '-I', '-c', "import sys; sys.argv=['x', %r]; "
        "exec(open('scratch/hdec-adopt3/dups.py').read())" % d], capture_output=True,
        text=True).stdout.splitlines()
    dup = {l.split()[1] for l in out if l.startswith('SAME')}
    tot = same = imp = 0; bad = []
    for n, p, i in decls(d):
        tot += 1
        if n in M:
            if blk(p, i) == blk(*M[n]): same += 1
            else: bad.append('DIFFERS ' + n)
        elif n in dup: imp += 1
        else: bad.append('MISSING ' + n)
    print(f'| {d.split("/")[-2]}/{d.split("/")[-1]} | {tot} | {same} | {imp} | {len(bad)} |')
    for b in bad: print('   ', b)
