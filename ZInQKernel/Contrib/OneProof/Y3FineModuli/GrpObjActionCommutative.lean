import ZInQKernel.Contrib.OneProof.Y3FineModuli.GrpObjActionTrace

/-!
# Relative commutativity follows from the actual unital additive order action

This is a new algebraic proof on the genuine over-category group object.
The additive action includes -1. Its endomorphism is the pointwise inverse
of the categorical identity; its actual IsMonHom property forces every
point group to commute. This proves the source RelativeGroupLaw commutativity
clause over arbitrary affine bases, without assuming CommGrpObj, fibrewise
geometric integrality, reducedness, a density lemma, or MumfordRigidity.
No group law, R1 witness, family or torsion cardinality is fabricated.
The existing source group-law constructor and Mathlib categorical group
operations are reused unchanged; all new work remains separate from PR40.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.OneProof.Y3FineModuli.Source

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open scoped CategoryTheory.MonObj

/-- The target-style genuine order-action clauses already imply the source's
all-test-scheme commutativity predicate. This is not a new commutativity premise. -/
theorem relativeGroupLaw_comm_of_order_action
    {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (act : LeafQM.O → (A ⟶ A)) (act_over : ∀ a, act a ≫ f = f)
    (act_hom : ∀ a : LeafQM.O,
      IsMonHom (Over.homMk (act a) (act_over a) : Over.mk f ⟶ Over.mk f))
    (act_one : act 1 = 𝟙 A)
    (act_add : ∀ a b : LeafQM.O,
      (Over.homMk (act (a + b)) (act_over _) : Over.mk f ⟶ Over.mk f) =
        Over.homMk (act a) (act_over a) * Over.homMk (act b) (act_over b)) :
    (relativeGroupLawOfGrpObj R f).IsCommutative := by
  let X := Over.mk f
  let α : LeafQM.O → (X ⟶ X) := fun a => Over.homMk (act a) (act_over a)
  have hzero : α 0 = (1 : X ⟶ X) := by
    have hh : α 0 = α 0 * α 0 := by
      simpa only [zero_add] using act_add 0 0
    have hc : α 0 * 1 = α 0 * α 0 := (mul_one (α 0)).trans hh
    exact (mul_left_cancel hc).symm
  have hone : α 1 = 𝟙 X := by
    apply Over.OverMorphism.ext
    exact act_one
  have hnegative : α (-1) = (𝟙 X : X ⟶ X)⁻¹ := by
    have hh : (𝟙 X : X ⟶ X) * α (-1) = 1 := by
      have h : α (1 + -1) = α 1 * α (-1) := act_add 1 (-1)
      rw [add_neg_cancel, hzero, hone] at h
      exact h.symm
    have hx := congrArg (fun s : X ⟶ X => (𝟙 X : X ⟶ X)⁻¹ * s) hh
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using hx
  haveI : IsMonHom ((𝟙 X : X ⟶ X)⁻¹) := by
    rw [← hnegative]
    exact act_hom (-1)
  intro T t P Q
  rw [relativeGroupLawOfGrpObj_mul, relativeGroupLawOfGrpObj_mul]
  apply congrArg (fun h : Over.mk t ⟶ X => overHomToSchemeHomOver h)
  let p : Over.mk t ⟶ X := schemeHomOverToOverHom P
  let q : Over.mk t ⟶ X := schemeHomOverToOverHom Q
  have hp : p⁻¹⁻¹ = p := _root_.inv_inv p
  have hq : q⁻¹⁻¹ = q := _root_.inv_inv q
  have hinv : (p⁻¹ * q⁻¹)⁻¹ = p * q := by
    have h := MonObj.mul_comp p⁻¹ q⁻¹ ((𝟙 X : X ⟶ X)⁻¹)
    simp only [GrpObj.comp_inv, Category.comp_id] at h
    rw [hp, hq] at h
    exact h
  have hreverse : (p⁻¹ * q⁻¹)⁻¹ = q * p := by
    rw [mul_inv_rev, hq, hp]
  exact hinv.symm.trans hreverse

end ZInQ.Contrib.OneProof.Y3FineModuli.Source
