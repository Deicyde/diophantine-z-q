"""leaf-fold: wrap the body of Leaves.lean in `namespace HDec` so that it can import ZInQKernel's
HDecomp/Contrib modules (which declare the same names at the root).

Usage: python3 scratch/leaf-fold/wrap.py BASE OUT
Edits (all mechanical):
 1. extra imports after the three base imports;
 2. `namespace HDec` before the first section, `end HDec` at the end of the file;
 3. declarations named `_root_.X` become `_root_.HDec.X`;
 4. dot-notation uses `t.lattice1` of the renamed `PeriodPair.lattice1` become explicit;
 5. `open ZInQ` (meant for the root namespace) becomes `open _root_.ZInQ`.
"""
import re, sys
src, out = sys.argv[1], sys.argv[2]
L = open(src).read().split('\n')
IMPORTS = """import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.Contrib.LocalKW.T30
import ZInQKernel.Contrib.KroneckerWeber.Leaves
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense
import ZInQKernel.Contrib.Different.Global
import ZInQKernel.Contrib.T25.NewformOfEigenform
import ZInQKernel.Contrib.T31.Main""".split('\n')
assert L[2].startswith('import ZInQKernel.Compiler')
L = L[:3] + IMPORTS + L[3:]
# namespace HDec before the first `section`
i0 = next(i for i, l in enumerate(L) if l.startswith('section PkgI1Sec'))
L = L[:i0] + ['namespace HDec', ''] + L[i0:]
txt = '\n'.join(L)
n3 = 0
def rootfix(m):
    global n3; n3 += 1
    return m.group(1) + '_root_.HDec.' + m.group(2)
txt = re.sub(r'^((?:noncomputable )?(?:def|theorem|lemma|abbrev|instance) )_root_\.([A-Za-z])', rootfix,
             txt, flags=re.M)
# lattice1 dot notation
n4 = 0
def latfix(m):
    global n4; n4 += 1
    return '(PeriodPair.lattice1 ' + m.group(1) + ')'
txt = re.sub(r'(\(L σ\)|\(Lp σ\)|\bL|gaussianPair)\.lattice1\b', latfix, txt)
n5 = len(re.findall(r'^open ZInQ\b(?!\.)', txt, flags=re.M))
txt = re.sub(r'^open ZInQ\b(?!\.)', 'open _root_.ZInQ', txt, flags=re.M)
# the one `open ZInQ` after `HDec.ZInQ` exists: open both halves of the former merged namespace
txt = txt.replace('open _root_.ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings',
                  'open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings')
txt = txt.rstrip('\n') + '\n\nend HDec\n'
open(out, 'w').write(txt)
print('root-renamed decls:', n3, ' lattice1 dot uses:', n4, ' open ZInQ:', n5)
