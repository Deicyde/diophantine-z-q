import ZInQKernel.Contrib.OneProof.CMBranch.R5Prune
import ZInQKernel.Contrib.OneProof.CMBranch.CoxProof

/-! # cm-branch2: the hand-fold of the manuscript's CM branch on the current top (dry run)

`HDec.HSyn.sixContactMin_of_open72_cm2_r5` (`CMBranch/R5Prune.lean`) is the current top theorem
`HDec.HSyn.sixContactMin_of_open72` (TailZ79) with

* the chain's base `sixContactMin_of_open4_hf_pz_eb` (FS5 / NoCM, from González–Rotger Thm 5.12, its count, the `X₆`
  Kummer fibre and `cmOptimalEmbedding`) replaced by cm-branch's `sixContactMin_of_open4_cm` (the manuscript's case
  split L578-580 and CM paragraph L581-631; diophantine_zq.tex);
* the glue `HeightAdditivityUpper` proved from the textbook field `t35` (`CMBranch/HeightAdd.lean`) and `ReducedCMPeriod`
  proved from `t35`, `homLatticeCorr`, `t11b` (`CMBranch/PeriodLattice.lean`, `CMBranch/ReducedPeriod.lean`) and Cox's
  lemma on proper ideals, itself proved (`CMBranch.coxProperLattice_proof`, `CMBranch/CoxProof.lean`);
* the moduli row carried in its weak form, the conjunct `R5ptProps` (González–Rotger Thm 5.12 on points of `X₆`) replaced by
  `True` in every bundle generation from `OpenResearchLeaves34EBCF` down (generated copies with suffix `_r5`), and the
  field `gonzalezRotgerX6Ab` of `OpenResearchLeaves34EBCF_r5` filled from `x6CoarseModuli` and
  `shimuraMainThmIDeligneY3AbU` (`QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse`): the top field
  `gonzalezRotgerThm512X6RCF` is still carried by the upper bundles but no longer read.

The remaining inputs are `c : CMBranch.CMInputs3`: the leaves `FowlerProp27`, `CMHeight62`, `CMjDegree`,
`CMPotentialGood` and the glue `CMFibreSplit`. -/

namespace HDec

namespace CMBranch
/-- **The CM-branch inputs still open after cm-branch2**: the leaves `FowlerProp27` (printed), `CMHeight62`,
`CMjDegree`, `CMPotentialGood` (consequence form) and the glue `CMFibreSplit` (docs/research/cm-branch2.md §4). -/
structure CMInputs3 : Prop where
  cmFibreSplit : CMFibreSplit
  fowlerProp27 : FowlerProp27
  cmjDegree : CMjDegree
  cmPotentialGood : CMPotentialGood
  cmHeight62 : CMHeight62
end CMBranch

namespace HSyn

/-- **Theorem 1.1's height hypothesis from the open statements and the CM-branch inputs** (cm-branch2 fold dry run). -/
theorem sixContactMin_of_open72_cmbranch2 (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  sixContactMin_of_open72_cm2_r5 r t l
    ⟨c.cmFibreSplit, c.fowlerProp27, c.cmjDegree, c.cmPotentialGood, c.cmHeight62, CMBranch.coxProperLattice_proof⟩

end HSyn

end HDec
