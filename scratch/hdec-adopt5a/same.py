# Check that each new module is its draft up to whitespace: drop `import` and `#print` lines and
# the adoption docstring, delete all whitespace, compare. Also check imports are the draft's.
import re
PAIRS = [('ModCurves/C9', 'scratch/c9-rhof/C9.lean'), ('ModCurves/E1Sub', 'scratch/e1-sub/E1Sub.lean'),
         ('ModCurves/X1Belyi', 'scratch/x1-belyi/X1Belyi.lean'),
         ('Faltings/HodgeLattice', 'scratch/hodge-lattice/HodgeLattice.lean'),
         ('Faltings/H5Neron', 'scratch/hdec-adopt5a/src/H5Neron.lean')]
def strip(t):
    t = re.sub(r'/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5a.*?-/',
               '', t, count=1, flags=re.S)
    t = '\n'.join(l for l in t.split('\n') if not l.startswith(('import ', '#print')))
    return re.sub(r'\s+', '', t)
ok = True
for m, d in PAIRS:
    a = open('ZInQKernel/HDecomp/' + m + '.lean').read(); b = open(d).read()
    ia = [l for l in a.split('\n') if l.startswith('import ')]
    ib = [l for l in b.split('\n') if l.startswith('import ')]
    same = strip(a) == strip(b) and ia == ib
    ok &= same
    print(('SAME ' if same else 'DIFF ') + m, len(a.split('\n')), 'lines')
print('ALL SAME' if ok else 'MISMATCH')
