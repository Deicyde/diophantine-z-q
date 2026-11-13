"""assemble-port: parts/e14_tshecke.lean = ts-hecke's TSHecke.lean (scratch/ts-hecke/assemble.py) without its three copies that
this file already has (PropTSGlue.lean L3-3553 = part e10; aut-o-finite's AutOFinite.lean = part a57; infra-smooth-dim's
SmoothStalk.lean, in b20/a70): curve-glue's `ComponentIrreducible` (CurveGlueAll.lean L1251-1253) + CIproof.lean.part in
`namespace CIcopy`, GenericFibre.lean, RamCount.lean, Units.lean, GaloisPart.lean.part, TSHeckeMain.lean.part, each verbatim
minus imports and `#print` lines, with the section wrappers of assemble.py; then mk/open_zinq.py. Run from scratch/assemble-port."""
import subprocess, sys
def lines(path, a, b):
    L = open(path).read().split('\n'); return '\n'.join(L[a-1:b]) + '\n'
def body(path, first):
    L = open(path).read().split('\n'); assert L[0].startswith(first), L[0]
    return '\n'.join(l for l in L[1:] if not l.startswith('#print'))
T = '../ts-hecke/'
out = ['/-! ## assemble-port: ts-hecke (scratch/ts-hecke/), its own parts without the copies this file has (mk/mk_tshecke.py) -/\n',
       '\nsection CICopy\n\nopen CategoryTheory AlgebraicGeometry\n\nnamespace CIcopy\n\n',
       lines('../curve-glue/CurveGlueAll.lean', 1251, 1253), '\n', open('../curve-glue/CIproof.lean.part').read(),
       '\nend CIcopy\n\nend CICopy\n',
       '\nsection GFCopy\n', body(T + 'GenericFibre.lean', 'import Mathlib'), '\nend GFCopy\n',
       '\nsection RamCountCopy\n', body(T + 'RamCount.lean', 'import Mathlib'), '\nend RamCountCopy\n',
       '\nsection UnitsCopy\n', body(T + 'Units.lean', 'import ZInQKernel.HDecomp.QM.Structures'), '\nend UnitsCopy\n',
       open(T + 'GaloisPart.lean.part').read(), '\nend\n',
       '\n'.join(l for l in open(T + 'TSHeckeMain.lean.part').read().split('\n') if not l.startswith('#print'))]
open('parts/e14_tshecke.lean', 'w').write(''.join(out))
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/e14_tshecke.lean'], check=True)
print('ok')
