import ZInQKernel.Contrib.OneProof.RC.GaussSign.Roots
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Gauss

/-! The signed quadratic Gauss evaluation for the manuscript's finite
additive character (tex 8640–8642, 8746–8753). The sign proof is
on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.GaussSign

open Intertwine Visibility WeilIndex Polynomial
open scoped BigOperators

private theorem negativeChar_eq_pow (p : ℕ) [NeZero p] (a : ZMod p) :
    negativeChar p a = negativeRoot p ^ a.val := by
  have hroot : negativeChar p 1 = negativeRoot p := by
    simp only [negativeChar, AddChar.mulShift_apply, mul_one, negativeRoot]
    rw [show (-1 : ZMod p) = ((-1 : ℤ) : ZMod p) by simp, ZMod.stdAddChar_coe]
    push_cast
    congr 1
    ring
  calc
    _ = negativeChar p (a.val • 1) := by rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    _ = _ := by rw [AddChar.map_nsmul_eq_pow, hroot]

private theorem exponentRoot_six : (exponentRoot (6 : ZMod 8) : ℂ) = -Complex.I := by
  change (zetaEight : ℂ) ^ (4 + 2 : ℕ) = _
  have h₄ : (zetaEight : ℂ) ^ 4 = -1 := by
    rw [← Units.val_pow_eq_pow_val, zetaEight_pow_four, Units.val_neg, Units.val_one]
  have h₂ : (zetaEight : ℂ) ^ 2 = Complex.I := by
    change Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) ^ 2 = _
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_pi_div_two_mul_I using 2
    ring
  rw [pow_add, h₄, h₂, neg_one_mul]

/-- Gauss's sign at every odd prime in the negative-character
normalization of the actual finite Weil index. -/
theorem oddGauss_one (p : Place) (hp : p.val ≠ 2) :
    oddGauss p 1 = (exponentRoot (oddBase (p.val : ZMod 4)) : ℂ) := by
  let m := p.val / 2
  have hodd := Nat.odd_iff.mp (p.property.odd_of_ne_two hp)
  have hm : 2 * m + 1 = p.val := by dsimp [m]; omega
  have hs : (Real.sqrt p.val : ℂ) ^ 2 = (p.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p.val)
  have hsne : (Real.sqrt p.val : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.mpr p.property.pos)).ne'
  have hG : aeval (negativeRoot p.val) (squarePolynomial p.val ℤ) = quadraticSum p.val 1 := by
    simp only [squarePolynomial, map_sum, map_pow, aeval_X, quadraticSum, one_mul,
      negativeChar_eq_pow]
  have hsq : (quadraticSum p.val 1) ^ 2 = (-1 : ℂ) ^ m * p.val := by
    have he := oddGauss_sq p hp 1
    rw [oddGauss, div_pow, hs, ZMod.χ₄_eq_neg_one_pow hodd, Int.cast_pow, Int.cast_neg,
      Int.cast_one] at he
    exact (div_eq_iff (Nat.cast_ne_zero.mpr p.property.ne_zero)).1 he
  have hProduct := eval_oddProduct_sq p.val m hm _ (negativeRoot_primitive p.val p.property.ne_zero)
  have hSign := eval_squarePolynomial_eq_of_sq p.val m hm (negativeRoot p.val)
    (negativeRoot_primitive p.val p.property.ne_zero) (by rw [hG, hsq, hProduct])
  rw [hG, eval_oddProduct_negativeRoot p.val m hm] at hSign
  rw [oddGauss, Units.val_one, hSign, mul_div_cancel_right₀ _ hsne]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [h, pow_zero, oddBase, ZMod.χ₄_nat_one_mod_four (show p.val % 4 = 1 by omega),
      ite_eq_right (by decide), exponentRoot_zero, Units.val_one]
  · have hχ : ZMod.χ₄ (p.val : ZMod 4) = -1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right (show p.val % 2 ≠ 0 by omega),
        ite_eq_right (show p.val % 4 ≠ 1 by omega)]
    rw [h, pow_one, oddBase, hχ, ite_eq_left rfl, exponentRoot_six]

#print axioms negativeChar_eq_pow
#print axioms exponentRoot_six
#print axioms oddGauss_one

end ZInQ.Manuscript.RC.GaussSign
