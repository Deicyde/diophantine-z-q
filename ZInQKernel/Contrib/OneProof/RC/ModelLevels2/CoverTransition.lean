import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.CoordinateEvaluation

/-! # Specialization of exact-order coordinates -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion
open scoped TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (W : WeierstrassCurve A) [W.IsElliptic] {N : ℕ} (hN : IsUnit (N : A))

/-- The ring map under the exact-order scalar extension, before extending
the scalars of its source. -/
noncomputable def exactOrderTransition :
    ExactOrderAlgebra W hN →+*
      ExactOrderAlgebra (W.map (algebraMap A B))
        (show IsUnit (N : B) by simpa only [map_natCast] using hN.map (algebraMap A B)) :=
  (exactOrderBaseChange (B := B) W hN).toRingHom.comp
    (Algebra.TensorProduct.includeRight (A := B)).toRingHom

set_option backward.isDefEq.respectTransparency false in
/-- The transition map carries the abscissa of the generator to the
abscissa of the specialized generator. -/
theorem exactOrderTransition_x {n : ℕ} (hn : IsUnit ((n + 3 : ℕ) : A)) :
    exactOrderTransition (B := B) W hn (generatorX W hn) =
      generatorX (W.map (algebraMap A B))
        (show IsUnit ((n + 3 : ℕ) : B) by simpa only [map_natCast] using hn.map (algebraMap A B)) := by
  change exactOrderBaseChange W hn
    ((1 : B) ⊗ₜ[A] affineToExactOrder W hn (torsionChartX W (n + 3))) = _
  simpa only [affineTorsionBaseChange_x, generatorX] using
    exactOrderBaseChange_affine W hn (1 : B) (torsionChartX W (n + 3))

set_option backward.isDefEq.respectTransparency false in
/-- The transition map carries the ordinate of the generator to the
ordinate of the specialized generator. -/
theorem exactOrderTransition_y {n : ℕ} (hn : IsUnit ((n + 3 : ℕ) : A)) :
    exactOrderTransition (B := B) W hn (generatorY W hn) =
      generatorY (W.map (algebraMap A B))
        (show IsUnit ((n + 3 : ℕ) : B) by simpa only [map_natCast] using hn.map (algebraMap A B)) := by
  change exactOrderBaseChange W hn
    ((1 : B) ⊗ₜ[A] affineToExactOrder W hn (torsionChartY W (n + 3))) = _
  simpa only [affineTorsionBaseChange_y, generatorY] using
    exactOrderBaseChange_affine W hn (1 : B) (torsionChartY W (n + 3))

#print axioms exactOrderTransition
#print axioms exactOrderTransition_x
#print axioms exactOrderTransition_y

end WeierstrassCurve.ModelLevels
