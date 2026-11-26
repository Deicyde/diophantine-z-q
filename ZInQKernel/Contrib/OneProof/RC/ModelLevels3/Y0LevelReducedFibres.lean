import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Smooth.Regular
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.QuotientPointLifts

/-! # Geometric reducedness of the pinned quotient -/

namespace WeierstrassCurve.ModelLevels.Pinned

open ModelTorsion RC.ModelInvariants
open scoped TensorProduct

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient)

private theorem detectorCover_smooth :
    Algebra.Smooth (LocalIntegers ell) (UniversalExactOrderAlgebra ell N h₅ htame) := by
  let R := LocalIntegers ell
  let P := MvPolynomial (Fin 2) R
  let A := ShortBase R
  let S := UniversalExactOrderAlgebra ell N h₅ htame
  letI : Algebra.Smooth P A := Algebra.Smooth.of_isLocalization_Away (shortEquation R).Δ
  letI : Algebra.Smooth R A := Algebra.Smooth.comp R P A
  letI : Algebra.Etale A S := (universalExactOrder_finite_etale ell N h₅ htame).2
  exact Algebra.Smooth.comp R A S

/-- The geometric cover is regular over each detector field. -/
theorem detectorCover_field_regular (k : Type*) [Field k] [Algebra (LocalIntegers ell) k] :
    IsRegularRing (k ⊗[LocalIntegers ell] UniversalExactOrderAlgebra ell N h₅ htame) := by
  letI := detectorCover_smooth h₅ htame
  exact Algebra.Smooth.isRegularRing k _

set_option backward.isDefEq.respectTransparency false in
/-- Over every detector field the pinned quotient ring is reduced. -/
theorem levelQuotient_fibre_reduced (h₂ : 2 ≤ N)
    (k : Type*) [Field k] [Algebra (LocalIntegers ell) k] :
    IsReduced (k ⊗[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂) := by
  let S := UniversalExactOrderAlgebra ell N h₅ htame
  let R := LocalIntegers ell
  letI := detectorCover_smooth h₅ htame
  letI : IsReduced (k ⊗[R] S) := Algebra.Smooth.isReduced_of_field k _
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  let e := levelQuotientBaseChange h₅ htame h₂ k
  letI := isReduced_of_injective
    (degreeZeroInvariantsInclusion (G := (ZMod N)ˣ)
      (fun i => (detectorExactOrderGrading h₅ htame h₂ i).baseChange k))
    (Subtype.val_injective.comp Subtype.val_injective)
  exact isReduced_of_injective e e.injective

#print axioms detectorCover_smooth
#print axioms detectorCover_field_regular
#print axioms levelQuotient_fibre_reduced

end WeierstrassCurve.ModelLevels.Pinned
