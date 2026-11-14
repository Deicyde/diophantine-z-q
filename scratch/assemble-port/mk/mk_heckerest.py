"""assemble-port: parts/e16_heckerest.lean = hecke-rest's new parts (scratch/hecke-rest/assemble.py, HeckeRestAll.lean below
its copies): FibreSizesMain, NoVertMain, CurveChartMain, InfFnMain, PointsMain, ProperMain, AllMain (.lean.part), verbatim
minus `#print` lines, in that order (as in HeckeRestAll.lean). Its copies are not repeated: TSHecke.lean (parts e10, e14,
a57, b20) and image-plane's AlgDepProof.lean L15-171, 277-322 (in part b20). Then mk/open_zinq.py and an `end` per unclosed
`noncomputable section`. Run from scratch/assemble-port."""
import re, subprocess, sys
H = '../hecke-rest/'
names = ['FibreSizesMain', 'NoVertMain', 'CurveChartMain', 'InfFnMain', 'PointsMain', 'ProperMain', 'AllMain']
src = {n: '\n'.join(l for l in open(H + n + '.lean.part').read().split('\n') if not l.startswith('#print')) for n in names}
# Statement versions. hecke-rest proved ts-hecke's `HeckeFibreSizes` as it stood before ts-hecke's commit 8015f0d6, which
# weakened it (dropped the first clause `∀ P, (twistFibre P).ncard ≤ M`). Part e14 has the current, weaker text. So
# hecke-rest's statement is added verbatim (FibreSizes.lean L1375-1381) as `HeckeFibreSizesHR`, `heckeFibreSizes_of` proves
# it (target renamed), and `heckeFibreSizes_of'` gives the current `HeckeFibreSizes` (drop the first clause); AllMain uses it.
old = 'theorem heckeFibreSizes_of (hT : ObjBridge.TorsionStructure) (hA : QMAutCard)\n    (hS : SerreRigidity3) (hW : ALFixedPoints) : HeckeFibreSizes := by'
assert src['FibreSizesMain'].count(old) == 1
fs = open(H + 'FibreSizes.lean').read().split('\n')
assert fs[1374].startswith('def HeckeFibreSizes : Prop :='), fs[1374]
hr = '\n'.join(fs[1374:1381]).replace('def HeckeFibreSizes : Prop :=', 'def HeckeFibreSizesHR : Prop :=')
src['FibreSizesMain'] = src['FibreSizesMain'].replace(old, old.replace(': HeckeFibreSizes := by', ': HeckeFibreSizesHR := by'))
doc = '/-- **`HeckeFibreSizes` from the leaves**'
assert src['FibreSizesMain'].count(doc) == 1
src['FibreSizesMain'] = src['FibreSizesMain'].replace(doc, '/-- hecke-rest\'s statement of `HeckeFibreSizes` (ts-hecke\'s text before 8015f0d6, verbatim; it has the extra first\n'
       'clause). -/\n' + hr + '\n\n' + doc)
end = 'end HeckeRest'
k = src['FibreSizesMain'].rindex(end)
src['FibreSizesMain'] = src['FibreSizesMain'][:k] + ('/-- ts-hecke\'s current `HeckeFibreSizes` from hecke-rest\'s stronger statement (drop its first clause). -/\n'
    'theorem heckeFibreSizes_of\' (hT : ObjBridge.TorsionStructure) (hA : QMAutCard)\n'
    '    (hS : SerreRigidity3) (hW : ALFixedPoints) : HeckeFibreSizes :=\n'
    '  let ⟨M, _, h1, h2, h3, h4⟩ := heckeFibreSizes_of hT hA hS hW\n  ⟨M, h1, h2, h3, h4⟩\n\n') + src['FibreSizesMain'][k:]
assert src['AllMain'].count('HeckeRest.heckeFibreSizes_of hT hA hS hW') == 3
src['AllMain'] = src['AllMain'].replace('HeckeRest.heckeFibreSizes_of hT hA hS hW', "HeckeRest.heckeFibreSizes_of' hT hA hS hW")
# Leaves.lean's `LeafQM.AV.bcPt`: here `bcPt` is ambiguous with curve-facts' `LeafQM.AV.Pin.bcPt` (part a56; `open ... Pin`)
b = src['FibreSizesMain']
assert b.count('bcPt X.A x') == 2 and b.count('rw [bcPt, ') == 1
b = b.replace('bcPt X.A x', 'LeafQM.AV.bcPt X.A x').replace('rw [bcPt, ', 'rw [LeafQM.AV.bcPt, ')
src['FibreSizesMain'] = b
txt = '/-! ## assemble-port: hecke-rest, its new parts (mk/mk_heckerest.py; two edits documented there) -/\n\n' + '\n'.join(src[n] for n in names)
k = len(re.findall(r'^noncomputable section\s*$', txt, re.M)) - len(re.findall(r'^end\s*$', txt, re.M))
txt += '\n' + '\nend  -- assemble-port: closes an unclosed `noncomputable section`\n' * max(0, k)
open('parts/e16_heckerest.lean', 'w').write(txt)
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/e16_heckerest.lean'], check=True)
print('ok', k)
