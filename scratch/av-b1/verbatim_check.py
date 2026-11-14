"""av-b1: check that the kernel's PkgI3 object layer (ZInQKernel/HDecomp/Objects.lean, over which
ZInQKernel/Contrib/AVB1/*.lean proves its theorems), the owner file scratch/pkg-I3/I3.lean, and
leaf-fold3's flat file (scratch/leaf-fold3/Leaves3.lean, namespace HDec.PkgI3) carry the same text
for every declaration the three fields t6, t7, t8 depend on.
Run from the repository root: python3 scratch/av-b1/verbatim_check.py"""
import re, sys
files = {'Objects': 'ZInQKernel/HDecomp/Objects.lean',
         'owner I3': 'scratch/pkg-I3/I3.lean',
         'Leaves3': 'scratch/leaf-fold3/Leaves3.lean'}
txt = {k: open(v).read() for k, v in files.items()}
# declaration heads (first occurrence after the PkgI3 namespace opens)
names = [r'def T\b', r'structure AbVar', r'def dim', r'def homGroup', r'abbrev Hom\b', r'def Hom.hom\b',
         r'abbrev End\b', r'instance \(A : AbVar K\) : Ring \(End A\)', r'abbrev End0', r'def IsIsogenyMor',
         r'def ptObj', r'abbrev Pt\b', r'def ptMap', r'abbrev T\b', r'abbrev V \(A : AbVar K\)', r'def homT',
         r'def tateHom\b', r'def tateHomZl', r'def baseChange \(A : AbVar K\)',
         r'def EndDivision', r'def HomFreeFinite', r'def CharPolyIndepOfEll', r'def PoincareReducibility',
         r'def smulSeq', r'instance : Module ℤ_\[ℓ\] \(T ℓ M\)', r'def map \(φ : M →\+ N\)']
def block(s, pat):
    m = re.search(r'^' + pat + r'.*?(?=\n\n|\n/--|\n@\[)', s, re.S | re.M)
    return m.group(0) if m else None
ok = True
for pat in names:
    bs = {k: block(s, pat) for k, s in txt.items()}
    same = len(set(bs.values())) == 1 and None not in bs.values()
    ok &= same
    print('%-45s %s' % (pat, 'IDENTICAL' if same else 'DIFFER ' + str({k: (b is not None) for k, b in bs.items()})))
print('ALL IDENTICAL' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
