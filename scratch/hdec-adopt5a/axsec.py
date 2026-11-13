# Append the hdec-adopt5a section of `#print axioms` lines to scripts/print_axioms.lean (once):
# the drafts' own targets (prints.txt, written by adopt5a.py) and a few main theorems the drafts
# did not print. Every name must be a declaration of the new modules.
import sys
sys.path.insert(0, 'scratch/hdec-adopt2')
from decls import decls
D = 'ZInQKernel/HDecomp/'
MODS = ['ModCurves/C9', 'ModCurves/E1Sub', 'ModCurves/X1Belyi', 'Faltings/HodgeLattice',
        'Faltings/H5Neron']
full = {n for m in MODS for n, p, i in decls(D + m + '.lean')}
names = [l.split()[1] for l in open('scratch/hdec-adopt5a/prints.txt')]
names += ['E1Sub.rhoF_semisimple_of_surj', 'X1Belyi.modCurveLeaves_of',
          'ZInQ.DefFaltings.HodgeLattice.tangentDimAtOrigin_of']
for n in names: assert n in full, n
assert len(set(names)) == len(names)
P = 'scripts/print_axioms.lean'
s = open(P).read()
assert 'hdec-adopt5a' not in s
s = s.rstrip('\n') + '\n'
s += ('\n-- hdec-adopt5a: c9-rhof, e1-sub, x1-belyi (`HDecomp.ModCurves.{C9,E1Sub,X1Belyi}`),\n'
      '-- hodge-lattice and h5-neron (`HDecomp.Faltings.{HodgeLattice,H5Neron}`).\n')
s += ''.join('#print axioms ' + n + '\n' for n in names)
open(P, 'w').write(s)
print(len(names))
