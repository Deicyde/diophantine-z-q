# pi0-fold: writes ZInQKernel/Contrib/OneProof/Pi0FoldSTQM.lean from STQM.lean (cm_point, stQM_of with the weak row)
src = open('ZInQKernel/Contrib/OneProof/STQM.lean').read().split('\n')
def grab(a, b): return '\n'.join(src[a-1:b])
cm = grab(756, 813)
st = grab(879, 904)
assert cm.startswith('/-- **A CM point') and 'theorem cm_point (hRep : HDec.LeafAdopt.R1R2fpRep)' in cm
assert st.startswith('/-- **`STQM`, proved**') and st.rstrip().endswith('rw [reassoc_of% h1, i.left]')
def rep(t, a, b):
    assert t.count(a) == 1, a
    return t.replace(a, b)
cm2 = rep(cm, 'theorem cm_point (hRep : HDec.LeafAdopt.R1R2fpRep)', 'theorem cm_pointW (hRep : HDec.LeafAdopt.R1R2fpRepW)')
cm2 = rep(cm2, 'h2, hr, hs, h5, -⟩ := hRep', 'h2, hr, hs, h5⟩ := hRep')
cm2 = rep(cm2, '/-- **A CM point of `Y₃(ℂ)` comes from `Y₃(ℚ̄)`**:', '/-- **A CM point of `Y₃(ℂ)` comes from `Y₃(ℚ̄)`** (`cm_point` with the weak row; pi0-fold):')
st2 = rep(st, 'theorem stQM_of (hRep : HDec.LeafAdopt.R1R2fpRep)', 'theorem stQM_ofW (hRep : HDec.LeafAdopt.R1R2fpRepW)')
st2 = rep(st2, '    cm_point hRep hconn', '    cm_pointW hRep hconn')
st2 = rep(st2, "* `hRep` — research field `r1r2` (`LeafAdopt.R1R2fpRep`);", "* `hRep` — research field `r1r2`, the weak row `LeafAdopt.R1R2fpRepW` (pi0-fold);")
st2 = rep(st2, '/-- **`STQM`, proved** (task st-qbar).', '/-- **`STQM`, proved** (task st-qbar; `stQM_of` with the weak row, pi0-fold).')
hdr = '''import ZInQKernel.Contrib.OneProof.STQM

/-! # pi0-fold: st-qbar's `STQM` from the weak row `R1R2fpRepW`

`GapST.cm_point` and `GapST.stQM_of` (STQM.lean, task st-qbar) take the row `HDec.LeafAdopt.R1R2fpRep` and discard
its last clause `R1pi0Props` (`X₆` geometrically connected). pi0-fold removes the two added leaves that produced that
clause, so the chain now carries the weak row `HDec.LeafAdopt.R1R2fpRepW` (LPrefix: `R1R2fpRep` without
`R1pi0Props`). This file restates the two theorems on the weak row; the proofs are st-qbar's, with the destructuring
pattern one conjunct shorter. The chain's `stQM` (TailX, `addedLeaves6_of_open7`) uses `stQM_ofW`.
(pi0-prune's scratch/pi0-prune/STQMW.lean compiled the same change.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace GapST
open _root_.LeafQM _root_.LeafQM.AV

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

'''
mid = '''

end Main

section Final

open MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

'''
ftr = '''

end Final

end GapST

#print axioms GapST.stQM_ofW
'''
open('ZInQKernel/Contrib/OneProof/Pi0FoldSTQM.lean', 'w').write(hdr + cm2 + mid + st2 + ftr)
