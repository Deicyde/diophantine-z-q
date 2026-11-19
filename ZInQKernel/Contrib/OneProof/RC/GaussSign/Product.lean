import ZInQKernel.Contrib.OneProof.RC.GaussSign.Sign
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Actual

/-! The signed local evaluation identifies the finite normalization used
by the oscillatory integral with the family used in scalar reciprocity.
This supplies the product-one factors of tex 9000–9004. -/

noncomputable section

namespace ZInQ.Manuscript.RC.GaussSign

open Intertwine Intertwine2 OldStageLaw Visibility WeilIndex

private theorem unit_sign_root (p : Place) (u : (ZMod p.val)ˣ) :
    (exponentRoot (signExponent (quadraticChar (ZMod p.val) (u : ZMod p.val))) : ℂ) =
      (quadraticChar (ZMod p.val) (u : ZMod p.val) : ℂ) := by
  rcases quadraticChar_dichotomy u.ne_zero with h | h
  · rw [h, signExponent, ite_eq_right (by decide), exponentRoot_zero, Units.val_one, Int.cast_one]
  · rw [h, signExponent, ite_eq_left rfl]
    change (zetaEight ^ 4 : ℂˣ).val = _
    rw [zetaEight_pow_four, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]

/-- The actual normalized finite oscillatory index agrees at every
place and coefficient with the explicit eighth-root formula. -/
theorem gaussGamma_eq_finiteGamma : gaussGamma = finiteGamma := by
  funext p a
  by_cases h : p ≠ dyadicPlace ∧ valAt p a % 2 ≠ 0
  · apply Units.ext
    rw [gaussGamma, dite_eq_left h, Units.val_mk0, finiteGamma, finiteExponent_odd p h.1,
      oddExponent, ite_eq_right h.2, exponentRoot_add, Units.val_mul, unit_sign_root]
    have hp : p.val ≠ 2 := fun he => h.1 (Subtype.ext he)
    rw [oddGauss_twist p hp, oddGauss_one p hp]
    exact mul_comm _ _
  · rw [gaussGamma, dite_eq_right h]

/-- Scalar reciprocity and diagonal multiplication give the product
formula for the actual finite family on any rational diagonal list. -/
theorem gaussGamma_productFormula : WeilIndexProductFormula gaussGamma := by
  rw [gaussGamma_eq_finiteGamma]
  exact finiteGamma_productFormula

/-- The product-one clauses for the rectangular form and the reference
form with the common real index used by the comparison. -/
theorem gaussGamma_rectangular_products (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)] :
    realIndex (rationalDiagonal a) * finiteIndex gaussGamma (rationalDiagonal a) = 1 ∧
      realIndex (rationalDiagonal a) * finiteIndex gaussGamma (rationalDiagonal referenceForm) = 1 :=
  index_products gaussGamma gaussGamma_productFormula a

#print axioms unit_sign_root
#print axioms gaussGamma_eq_finiteGamma
#print axioms gaussGamma_productFormula
#print axioms gaussGamma_rectangular_products

end ZInQ.Manuscript.RC.GaussSign
