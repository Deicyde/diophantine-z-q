import ZInQKernel.Size.Norms.Defs

/-!
# Elementary estimates for the coefficient norm

Blueprint: `size/norms/l1-norm-estimates.md`.

Most estimates are in `ZInQKernel/Syntax/Language/Size.lean` (`natAbs_coeff_le_l1`, `l1_C`,
`l1_X`, `l1_neg`, `l1_add_le`, `l1_mul_le`, `l1_pow_le`, `l1_finset_sum_le`,
`l1_finset_prod_le`) and the degree bounds are Mathlib's. Here we add the missing ones
(`l1_eq_zero_iff`, `l1_C_mul`, `l1_smul`) and collect everything in `l1_estimates`.
-/

namespace ZInQ.Size

open MvPolynomial
open ZInQ.Syntax (l1 l1_C l1_X l1_neg l1_add_le l1_mul_le l1_pow_le l1_finset_sum_le
  l1_finset_prod_le natAbs_coeff_le_l1 l1_zero)

variable {σ : Type*}

/-- `‖f‖₁ = 0` only for `f = 0`. -/
theorem l1_eq_zero_iff (f : MvPolynomial σ ℤ) : l1 f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ l1_zero⟩
  ext d
  have := natAbs_coeff_le_l1 f d
  show f.coeff d = 0
  omega

theorem l1_pos {f : MvPolynomial σ ℤ} (hf : f ≠ 0) : 0 < l1 f :=
  Nat.pos_of_ne_zero fun h => hf ((l1_eq_zero_iff f).1 h)

/-- `‖c • f‖₁ = |c| ‖f‖₁`. -/
theorem l1_smul (c : ℤ) (f : MvPolynomial σ ℤ) : l1 (c • f) = c.natAbs * l1 f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [Syntax.l1, Syntax.l1, support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coeff_smul, smul_eq_mul, Int.natAbs_mul]

/-- `‖c f‖₁ = |c| ‖f‖₁`. -/
theorem l1_C_mul (c : ℤ) (f : MvPolynomial σ ℤ) : l1 (C c * f) = c.natAbs * l1 f := by
  rw [C_mul', l1_smul]

theorem l1_natCast (n : ℕ) : l1 (n : MvPolynomial σ ℤ) = n := by
  rw [← map_natCast (C : ℤ →+* MvPolynomial σ ℤ), l1_C, Int.natAbs_natCast]

theorem l1_ofNat (n : ℕ) [n.AtLeastTwo] : l1 (OfNat.ofNat n : MvPolynomial σ ℤ) = n :=
  l1_natCast n

theorem l1_intCast (n : ℤ) : l1 (n : MvPolynomial σ ℤ) = n.natAbs := by
  rw [← map_intCast (C : ℤ →+* MvPolynomial σ ℤ), l1_C, Int.cast_id]

/-- **Elementary estimates.** (1) `|[X^α] f| ≤ ‖f‖₁` and `‖f‖₁ = 0` only for `f = 0`;
(2) `‖c‖₁ = |c|`, `‖X_i‖₁ = 1`, `‖-f‖₁ = ‖f‖₁`, `‖c f‖₁ = |c| ‖f‖₁`; (3) `‖f + g‖₁ ≤ ‖f‖₁ + ‖g‖₁`,
`‖f g‖₁ ≤ ‖f‖₁ ‖g‖₁`, `‖f^k‖₁ ≤ ‖f‖₁^k`, and the same for finite sums and products;
(4) `deg (f + g) ≤ max (deg f) (deg g)`, `deg (f g) ≤ deg f + deg g`, `deg f^k ≤ k deg f`,
`deg c = 0`, `deg X_i ≤ 1`, and the same for finite sums and products. -/
theorem l1_estimates {ι : Type*} (f g : MvPolynomial σ ℤ) (c : ℤ) (i : σ) (k : ℕ)
    (s : Finset ι) (F : ι → MvPolynomial σ ℤ) :
    ((∀ α, (f.coeff α).natAbs ≤ l1 f) ∧ (l1 f = 0 ↔ f = 0)) ∧
    (l1 (C c : MvPolynomial σ ℤ) = c.natAbs ∧ l1 (X i : MvPolynomial σ ℤ) = 1 ∧
      l1 (-f) = l1 f ∧ l1 (C c * f) = c.natAbs * l1 f) ∧
    (l1 (f + g) ≤ l1 f + l1 g ∧ l1 (f * g) ≤ l1 f * l1 g ∧ l1 (f ^ k) ≤ l1 f ^ k ∧
      l1 (∑ j ∈ s, F j) ≤ ∑ j ∈ s, l1 (F j) ∧ l1 (∏ j ∈ s, F j) ≤ ∏ j ∈ s, l1 (F j)) ∧
    ((f + g).totalDegree ≤ max f.totalDegree g.totalDegree ∧
      (f * g).totalDegree ≤ f.totalDegree + g.totalDegree ∧
      (f ^ k).totalDegree ≤ k * f.totalDegree ∧
      (C c : MvPolynomial σ ℤ).totalDegree = 0 ∧ (X i : MvPolynomial σ ℤ).totalDegree ≤ 1 ∧
      (∑ j ∈ s, F j).totalDegree ≤ s.sup (fun j => (F j).totalDegree) ∧
      (∏ j ∈ s, F j).totalDegree ≤ ∑ j ∈ s, (F j).totalDegree) :=
  ⟨⟨natAbs_coeff_le_l1 f, l1_eq_zero_iff f⟩, ⟨l1_C c, l1_X i, l1_neg f, l1_C_mul c f⟩,
    ⟨l1_add_le f g, l1_mul_le f g, l1_pow_le f k, l1_finset_sum_le s F, l1_finset_prod_le s F⟩,
    ⟨totalDegree_add f g, totalDegree_mul f g, totalDegree_pow f k, totalDegree_C c,
      (totalDegree_X i).le, totalDegree_finsetSum s F, totalDegree_finsetProd s F⟩⟩

end ZInQ.Size
