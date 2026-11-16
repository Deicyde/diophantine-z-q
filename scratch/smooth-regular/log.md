# smooth-regular results log

Base: e22df37cd (fork main after leaf-fold30). Build tree copied from ~/dzq-wt/isj1-dict, then
`lake build ZInQKernel.OneProof.H.TailR ...RingTheory.Smooth.RegularLocalRing ...Morphisms.SmoothSourceDescent`
(EXIT 0, build1.log).

## Step 1. `CurveSplit.RegularSmoothPerfect` (open field `OpenTextbookLeaves11.regularSmoothPerfect`, Stacks 00TV ⇐)

* VERIFIED (compiled, T1.lean, axioms propext/Classical.choice/Quot.sound): theorem
  `regularSmoothPerfect_proof : CurveSplit.RegularSmoothPerfect`, 5 lines, from
  `Algebra.FormallySmooth.localization_of_isRegularLocalRing` (vendored Jacobian-Challenge,
  ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/RingTheory/Smooth/RegularLocalRing.lean),
  Mathlib's `Algebra.FormallySmooth.of_perfectField` (residue field ess. finite type over a perfect field)
  and Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth` (smooth locus open).
  Needs `set_option backward.isDefEq.respectTransparency false` for the residue-field EssFiniteType instance.
