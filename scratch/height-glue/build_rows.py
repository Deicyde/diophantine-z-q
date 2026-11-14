#!/usr/bin/env python3
"""Assemble scratch/height-glue/Rows.lean and part_rows.lean.

Rows.lean = scratch/height-split/HeightSplit.lean lines 3-919 (verbatim, task height-split; its
`namespace ZInQ.HeightSplit ... end ZInQ.HeightSplit` body without imports and axiom checks)
+ base/Kernel_metrization2.lean + base/JacDescends_unifdims.lean + AUUnique.lean + part_main.lean
+ part_rows.lean (= part_neron.lean without its verbatim copies of height-split's Props, which in
Rows.lean are height-split's own, plus `heightRows_of_t35`).
The only edit to copied text: bare `AbVar` in the appended (non-HeightSplit) parts is written
`PkgI3.AbVar`, because HeightBC's alias `DefFaltings.AbVar := PkgI3.AbVar` is also in scope (same
type, removes an ambiguity)."""
D = 'scratch/height-glue/'
pn = open(D + 'part_neron.lean').read()
i = pn.index("\nend ZInQ.HeightGlue\n")
j = pn.index("namespace ZInQ.HeightGlue\n", i)
j2 = pn.index("\n", pn.index("set_option linter.style.haveILetI false", j))
rows = pn[:i] + "\n\nopen ZInQ.HeightSplit\n" + pn[j2:]
rows += '''
/-- **The six height rows (H-14 to H-19) from height-split's nine published-form leaves and the
textbook leaf T35 alone** (proved): height-split's `heightRows_of` with its glue bundle
`HeightGlue` supplied by `heightGlue_of_t35`. -/
theorem heightRows_of_t35 (l : ZInQ.HeightSplit.HeightLeaves)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.LeafPush2.R18_Javanpeykar ∧ ZInQ.DefFaltings.R19_GaudronRemond ∧
      ZInQ.DefFaltings.R20_FaltingsLemma5 ∧ ZInQ.DefFaltings.R21_Bost ∧
      ZInQ.LeafPush2.R22_Pazuki ∧ ZInQ.DefFaltings.StableHeightFinite :=
  ZInQ.HeightSplit.heightRows_of l (heightGlue_of_t35 hT35)
'''
open(D + 'part_rows.lean', 'w').write(rows)
hs = open('scratch/height-split/HeightSplit.lean').read().split('\n')
assert hs[28].startswith('namespace ZInQ.HeightSplit') and hs[918].startswith('end ZInQ.HeightSplit')
body = hs[2:919]
k = open(D + 'base/Kernel_metrization2.lean').read().split('\n')
k = [l for l in k if not l.startswith('import ') and not l.startswith('#print')]
jd = open(D + 'base/JacDescends_unifdims.lean').read().split('\n')
a = open(D + 'AUUnique.lean').read().split('\n')
a = [l for l in a if not l.startswith('import ') and not l.startswith('#print')]
while a and a[-1].strip() == '':
    a.pop()
assert a[-1].startswith('end ZInQ.HeightGlue')
a.pop()
pm = open(D + 'part_main.lean').read().split('\n')
hdr = ['import ZInQKernel.HDecomp.LeafPush2.R22', 'import ZInQKernel.Contrib.HeightBC.Main',
       'import ZInQKernel.HDecomp.LeafPush2.T', 'import ZInQKernel.Contrib.Dim.HodgeLattice',
       'import ZInQKernel.HDecomp.Faltings.H5Neron', '',
       "/-! # height-glue: the six height rows from height-split's leaves and T35.",
       'Assembled by `build_rows.py` (see its docstring for the verbatim sources). -/', '']
import re
def fix(lines):
    # `DefFaltings.AbVar` (HeightBC) and `PkgI3.AbVar` are both in scope here: qualify bare uses.
    return [re.sub(r'(?<![\w.])AbVar(?=[ )\]])', 'PkgI3.AbVar', l) if not l.lstrip().startswith('open') else l
            for l in lines]
out = hdr + body + fix(k) + fix(jd) + fix(a) + fix(pm) + fix(rows.split('\n')) + [
    'end ZInQ.HeightGlue', '',
    '#print axioms ZInQ.HeightGlue.heightRows_of_t35',
    '#print axioms ZInQ.HeightGlue.heightGlue_of_t35']
open(D + 'Rows.lean', 'w').write('\n'.join(out) + '\n')
