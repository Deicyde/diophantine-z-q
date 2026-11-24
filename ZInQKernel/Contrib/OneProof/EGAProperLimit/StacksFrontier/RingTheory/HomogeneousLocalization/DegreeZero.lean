/-
Ported from AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/RingTheory/HomogeneousLocalization/DegreeZero.lean
Upstream license: Apache-2.0; see EGAProperLimit/LICENSE.
Modified for the Z-in-Q kernel (ega-limit, 2026-11-16): import paths remapped into EGAProperLimit (modules already
vendored in CloudW01Spread are imported from there); the upstream lakefile option
`maxSynthPendingDepth = 3` is set in the file; four declaration names that clash with
CloudW07JacobiansCurves are renamed (ProjectiveSpace -> StacksProjectiveSpace, and three
lemmas get the suffix _stacks; see NOTICE.md). The mathematical content and proofs are unchanged.
-/
module

public import ZInQKernel.Contrib.OneProof.EGAProperLimit.StacksFrontier.RingTheory.HomogeneousLocalization.DegreeZero.Construction
public import ZInQKernel.Contrib.OneProof.EGAProperLimit.StacksFrontier.RingTheory.HomogeneousLocalization.DegreeZero.Finiteness
public import ZInQKernel.Contrib.OneProof.EGAProperLimit.StacksFrontier.RingTheory.HomogeneousLocalization.DegreeZero.AtPrime

-- Port: the upstream lakefile sets `maxSynthPendingDepth = 3` for every file.
set_option maxSynthPendingDepth 3
