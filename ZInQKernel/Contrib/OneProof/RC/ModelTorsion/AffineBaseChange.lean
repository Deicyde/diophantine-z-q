import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.AffineAlgebra
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Base change and the ordinate on the two-torsion branch -/

namespace WeierstrassCurve.ModelTorsion

open Polynomial
open scoped TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B]

private noncomputable def quadraticChartBaseChange [Algebra A B]
    (W : WeierstrassCurve A) (n : ℕ) :
    B ⊗[A] AdjoinRoot (unramifiedOrdinate W n) ≃ₐ[B]
      AdjoinRoot (unramifiedOrdinate (W.map (algebraMap A B)) n) := by
  let f := W.preΨ' n
  let f' := (W.map (algebraMap A B)).preΨ' n
  let q := unramifiedOrdinate W n
  let q' := unramifiedOrdinate (W.map (algebraMap A B)) n
  let i : AdjoinRoot f →ₐ[A] B ⊗[A] AdjoinRoot f := Algebra.TensorProduct.includeRight
  let e : B ⊗[A] AdjoinRoot f ≃ₐ[B] AdjoinRoot f' :=
    (polynomialQuotientBaseChange f).trans
      (AdjoinRoot.algEquivOfEq B _ _ (W.map_preΨ' (algebraMap A B) n).symm)
  refine (AdjoinRoot.tensorAlgEquiv q (q.map i.toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv e _ q' ?_)
  change Associated ((q.map i.toRingHom).map e.toRingHom) q'
  suffices h : (q.map i.toRingHom).map e.toRingHom = q' from h ▸ Associated.refl q'
  rw [Polynomial.map_map]
  change (ordinatePolynomial (W.map (algebraMap A (AdjoinRoot f))) (AdjoinRoot.root f)).map
    (e.toRingHom.comp i.toRingHom) = q'
  rw [map_ordinatePolynomial, WeierstrassCurve.map_map]
  have hcoeff : (e.toRingHom.comp i.toRingHom).comp (algebraMap A (AdjoinRoot f)) =
      algebraMap A (AdjoinRoot f') := by
    ext a
    change e (1 ⊗ₜ algebraMap A (AdjoinRoot f) a) = algebraMap A (AdjoinRoot f') a
    rw [← Algebra.TensorProduct.algebraMap_apply']
    exact (e.restrictScalars A).commutes a
  have hroot : e (1 ⊗ₜ AdjoinRoot.root f) = AdjoinRoot.root f' := by
    dsimp only [e]
    rw [AlgEquiv.trans_apply, polynomialQuotientBaseChange_root, AdjoinRoot.algEquivOfEq_root]
  rw [hcoeff]
  change ordinatePolynomial (W.map (algebraMap A (AdjoinRoot f'))) _ = q'
  rw [show (e.toRingHom.comp i.toRingHom) (AdjoinRoot.root f) =
    AdjoinRoot.root f' from hroot]
  unfold q' unramifiedOrdinate
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

/-- Both affine charts commute with extension of scalars. -/
noncomputable def affineTorsionAlgebraBaseChange [Algebra A B] (W : WeierstrassCurve A) (n : ℕ) :
    B ⊗[A] AffineTorsionAlgebra W n ≃ₐ[B]
      AffineTorsionAlgebra (W.map (algebraMap A B)) n := by
  have hbranch : (branchPolynomial W n).map (algebraMap A B) =
      branchPolynomial (W.map (algebraMap A B)) n := by
    by_cases h : Even n <;> simp [branchPolynomial, h, W.map_Ψ₂Sq]
  exact (Algebra.TensorProduct.prodRight A B B _ _).trans
    (AlgEquiv.prodCongr (quadraticChartBaseChange W n)
      ((polynomialQuotientBaseChange (branchPolynomial W n)).trans
        (AdjoinRoot.algEquivOfEq B _ _ hbranch)))

private theorem four_mul_ordinate_value (W : WeierstrassCurve A) (x y : A) :
    4 * (ordinatePolynomial W x).eval y =
      (2 * y + (W.a₁ * x + W.a₃)) ^ 2 - W.Ψ₂Sq.eval x := by
  simp only [ordinatePolynomial, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- With two invertible, the branch equation is precisely the existence of
a unique ordinate satisfying both the curve equation and the vertical
two-torsion condition. -/
theorem branch_eq_zero_iff_existsUnique_ordinate (W : WeierstrassCurve A)
    (h₂ : IsUnit (2 : A)) (x : A) :
    W.Ψ₂Sq.eval x = 0 ↔
      ∃! y, W.toAffine.Equation x y ∧ 2 * y + (W.a₁ * x + W.a₃) = 0 := by
  let r := W.a₁ * x + W.a₃
  let z := -(↑(h₂.unit⁻¹) * r)
  have hi : (2 : A) * ↑(h₂.unit⁻¹) = 1 := by
    calc
      (2 : A) * ↑(h₂.unit⁻¹) = ↑h₂.unit * ↑(h₂.unit⁻¹) :=
        congrArg (· * ↑(h₂.unit⁻¹)) h₂.unit_spec.symm
      _ = 1 := by simp
  have hz : 2 * z + r = 0 := by
    dsimp [z]
    rw [mul_neg, ← mul_assoc, hi, one_mul, neg_add_cancel]
  constructor
  · intro hx
    have h₄ : IsUnit (4 : A) := by
      simpa only [show (2 : A) * 2 = 4 by ring] using h₂.mul h₂
    have hval := four_mul_ordinate_value W x z
    change 4 * (ordinatePolynomial W x).eval z = (2 * z + r) ^ 2 - W.Ψ₂Sq.eval x at hval
    rw [hz, hx, zero_pow two_ne_zero, sub_zero] at hval
    refine ⟨z, ⟨(eval_ordinatePolynomial_eq_zero_iff W x z).1
      (h₄.mul_right_inj.mp (hval.trans (mul_zero _).symm)), hz⟩, ?_⟩
    rintro y ⟨_, hy⟩
    apply h₂.mul_right_inj.mp
    exact add_right_cancel (hy.trans hz.symm)
  · rintro ⟨y, ⟨hy, hy'⟩, _⟩
    have h := four_mul_ordinate_value W x y
    rw [(eval_ordinatePolynomial_eq_zero_iff W x y).2 hy, hy', zero_pow two_ne_zero,
      mul_zero, zero_sub] at h
    exact neg_eq_zero.mp h.symm

#print axioms four_mul_ordinate_value
#print axioms branch_eq_zero_iff_existsUnique_ordinate

end WeierstrassCurve.ModelTorsion
