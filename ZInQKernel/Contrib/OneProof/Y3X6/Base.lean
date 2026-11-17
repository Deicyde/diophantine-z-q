import ZInQKernel.OneProof.H.TailZ79
import ZInQKernel.Contrib.OneProof.CMBranch.Open4
import ZInQKernel.Contrib.OneProof.CMBranch.HeightAdd
import ZInQKernel.Contrib.OneProof.CMBranch.PeriodLattice
import ZInQKernel.Contrib.OneProof.CMBranch.CoxProof
import ZInQKernel.Contrib.OneProof.Y3ToP1j

/-! # y3-x6: the CM-branch inputs of cm-branch2 (verbatim copy of `CMBranch.CMInputs2`, CMBranch/Top2.lean 25-34)

On the merged tree (cm-branch d4073125e) `CMBranch/Top2.lean` no longer compiles: `sixContactMin_of_open4_cm` now takes
`CMHomFieldSplit` (cm-branch reduced `CMFibreSplit` to it, `CMBranch/A8.lean`), while Top2 passes `CMFibreSplit`. The
y3-x6 copies use only cm-branch2's `_r5` copies of the chain (which carry their own copy of `sixContactMin_of_open4_cm`
taking `CMFibreSplit`) and this structure, so they do not import Top2. -/

namespace HDec
set_option maxHeartbeats 1000000
noncomputable section

namespace CMBranch
/-- **The CM-branch inputs still open** (docs/research/cm-branch2.md): the leaves `FowlerProp27`, `CMHeight62`,
`CMjDegree`, `CMPotentialGood`, `CoxProperLattice` and the glue `CMFibreSplit`. -/
structure CMInputs2 : Prop where
  cmFibreSplit : CMFibreSplit
  fowlerProp27 : FowlerProp27
  cmjDegree : CMjDegree
  cmPotentialGood : CMPotentialGood
  cmHeight62 : CMHeight62
  coxProperLattice : CoxProperLattice
end CMBranch
end
end HDec
