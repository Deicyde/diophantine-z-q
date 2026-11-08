import ZInQKernel.Progressions.Mertens.Defs

/-!
# Orthogonality: `S_a` as a combination of the `S_χ`

For `a` a unit modulo `q`, `S_a(x) = (1/φ(q)) Σ_χ χ(a⁻¹) S_χ(x)`, where `χ(a⁻¹) = χ(a)⁻¹`.
-/

namespace ZInQ.Progressions

open Finset
open ArithmeticFunction hiding log

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Orthogonality**: `S_a(x) = (1/φ(q)) Σ_χ χ(a)⁻¹ S_χ(x)` for `a` coprime to `q`. -/
theorem classSum_eq_sum_twistedSum (ha : IsUnit a) (x : ℝ) :
    (classSum a x : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * twistedSum χ x := by
  have h : classSum a x = ∑ n ∈ Ioc 0 ⌊x⌋₊, vonMangoldt.residueClass a n / n := by
    rw [classSum, sum_filter]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp
  rw [h]
  push_cast
  simp_rw [vonMangoldt.residueClass_apply ha, twistedSum, mul_sum, sum_div, mul_div_assoc]
  rw [sum_comm]
  refine sum_congr rfl fun n _ ↦ sum_congr rfl fun χ _ ↦ ?_
  ring

omit [NeZero q] in
/-- `χ(a⁻¹) = χ(a)⁻¹` for a unit `a`. -/
lemma dirichletCharacter_apply_inv_of_isUnit (χ : DirichletCharacter ℂ q) (ha : IsUnit a) :
    χ a⁻¹ = (χ a)⁻¹ := by
  have h1 : χ a⁻¹ * χ a = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit a ha, map_one]
  exact eq_inv_of_mul_eq_one_left h1

/-- The difference `S_a(x) − S_a(y)` through the character sums. -/
theorem classSum_sub_eq (ha : IsUnit a) (x y : ℝ) :
    classSum a x - classSum a y =
      (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (twistedSum χ x - twistedSum χ y)).re := by
  have h := congrArg Complex.re (congrArg₂ (· - ·) (classSum_eq_sum_twistedSum ha x)
    (classSum_eq_sum_twistedSum ha y))
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  rw [h, ← Complex.sub_re, ← mul_sub, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [show ((q.totient : ℂ))⁻¹ = (((q.totient : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]

end ZInQ.Progressions
