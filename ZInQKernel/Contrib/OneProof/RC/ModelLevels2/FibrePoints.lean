import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.BaseChange
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ExactOrderPoints

/-! # Field readings of the exact-order cover -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion
open scoped TensorProduct

variable {A k : Type*} [CommRing A] [Field k] [Algebra A k]

/-- An algebra map on the exact-order cover over a chosen field-valued
coefficient point gives a point of that exact order on the specialized
curve. This includes residue fields of positive characteristic in which
the level is invertible. -/
noncomputable def exactOrderFibrePoints [DecidableEq k]
    (W : WeierstrassCurve A) [W.IsElliptic] {N : ℕ} (hN : IsUnit (N : A)) :
    (ExactOrderAlgebra W hN →ₐ[A] k) ≃
      {P : (W.map (algebraMap A k)).toAffine.Point // addOrderOf P = N} := by
  let V := W.map (algebraMap A k)
  have hNk : IsUnit (N : k) := by simpa only [map_natCast] using hN.map (algebraMap A k)
  let e := exactOrderBaseChange (B := k) W hN
  exact (AlgHom.liftEquiv A k _ k).trans
    ((AlgEquiv.arrowCongr e (AlgEquiv.refl : k ≃ₐ[k] k)).trans (exactOrderPoints V hNk))

section AffineRestriction

variable {B : Type*} [CommRing B] [Algebra A B]

/-- For affine levels, the morphism on rings cutting out exact order is
the localization at the product of the proper-divisor idempotents. -/
noncomputable def affineToExactOrder (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hN : IsUnit ((n + 2 : ℕ) : A)) :
    AffineTorsionAlgebra W (n + 2) →ₐ[A] ExactOrderAlgebra W hN :=
  IsScalarTower.toAlgHom A (AffineTorsionAlgebra W (n + 2))
    (ClopenFactor (exactOrderIdempotent W hN))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison on the affine complement carries its numerators to
the corresponding numerators in the specialized charts. -/
theorem exactOrderBaseChange_affine (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hN : IsUnit ((n + 2 : ℕ) : A))
    (b : B) (x : AffineTorsionAlgebra W (n + 2)) :
    let V := W.map (algebraMap A B)
    let hNB : IsUnit ((n + 2 : ℕ) : B) := by
      simpa only [map_natCast] using hN.map (algebraMap A B)
    exactOrderBaseChange (B := B) W hN (b ⊗ₜ[A] affineToExactOrder W hN x) =
      affineToExactOrder V hNB (affineTorsionAlgebraBaseChange W (n + 2) (b ⊗ₜ[A] x)) := by
  dsimp only [affineToExactOrder, exactOrderBaseChange, exactOrderBaseChangeOfRestriction]
  erw [AlgEquiv.trans_apply (clopenFactorBaseChange (A := A) B (exactOrderIdempotent W hN)),
    clopenFactorBaseChange_tmul (A := A) B (exactOrderIdempotent W hN) x b]
  apply IsLocalization.algEquivOfAlgEquiv_eq (Q := ClopenFactor (exactOrderIdempotent
    (W.map (algebraMap A B)) (show IsUnit ((n + 2 : ℕ) : B) by
      simpa only [map_natCast] using hN.map (algebraMap A B))))

end AffineRestriction

#print axioms exactOrderFibrePoints
#print axioms affineToExactOrder
#print axioms exactOrderBaseChange_affine

end WeierstrassCurve.ModelLevels
