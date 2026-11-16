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

## Step 2. Scheme forms (ZInQKernel/Contrib/OneProof/SmoothRegular/Basic.lean)

VERIFIED (lake build, axioms standard; T2.lean then Basic.lean, T3.lean prints axioms), `X` locally of finite type over a field `K`:
* `smooth_iff_isRegularLocalRing_stalk` (K perfect): Smooth ↔ all stalks regular.
* `smooth_iff_nonsingular` (K perfect): Smooth ↔ stalks at closed points regular (Jacobson + open smooth locus).
* `smooth_iff_geometricallyRegular` (any K): Smooth ↔ X_L regular for every field ext L/K (Type u).
* `smooth_iff_regularAfter_algebraicClosure`, `smooth_iff_nonsingularAfter_algebraicClosure` (any K):
  Smooth ↔ X_{K̄} regular ↔ X_{K̄} regular at closed points (fpqc descent of smoothness, Mathlib).
* `smooth_tfae_perfect`: smooth / regular / geometrically regular TFAE over a perfect field.
* Dictionary: `abVarOfNonsingular`, `abVarOfNonsingularAfter` (packaging into PkgI3.AbVar),
  `exists_abVar_iff_nonsingular`, `exists_abVar_iff_nonsingularAfter`.

## Step 3. Contribution file ZInQKernel/Contrib/OneProof/RegularSmoothPerfect.lean

VERIFIED (lake build ZInQKernel.Contrib.OneProof.RegularSmoothPerfect OK; axioms propext, Classical.choice, Quot.sound):
* `ZInQ.Contrib.SmoothRegular.regularSmoothPerfect : CurveSplit.RegularSmoothPerfect` (no hypotheses).
* `ZInQ.Contrib.SmoothRegular.isRegularLocalRing_of_smooth` (00TV ⇒, algebraic form, any field).
