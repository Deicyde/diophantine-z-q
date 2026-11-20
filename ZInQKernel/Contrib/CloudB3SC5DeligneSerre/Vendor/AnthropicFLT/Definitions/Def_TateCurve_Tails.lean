/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_TateCurve_Tails (git blob bbcd325d897e835918b0f2632991122fa05349ad, sha256 96409fa08feefc62b7c0b4277529fc2dfa653aeeecdef98037a3bfa5f2bf68f1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist

namespace TateCurve

section Coefficients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

private theorem norm_add_le_max' (a b : K) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  exact_mod_cast nnnorm_add_le_max a b

private theorem norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa [norm_neg] using norm_add_le_max' a (-b)

noncomputable def xDivTerm (u : K) (d : ℕ) : K := (d : K) * (u ^ d + u⁻¹ ^ d - 2)

noncomputable def yDivTerm (u : K) (d : ℕ) : K :=
  ((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d) - (d : K) * u⁻¹ ^ d + (d : K)

noncomputable def xCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, xDivTerm u d

noncomputable def yCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, yDivTerm u d

noncomputable def growthBound (u : K) : ℝ := max (max ‖u‖ ‖u⁻¹‖) 1

theorem one_le_growthBound (u : K) : 1 ≤ growthBound u := le_max_right _ _

theorem growthBound_nonneg (u : K) : 0 ≤ growthBound u :=
  zero_le_one.trans (one_le_growthBound u)

theorem norm_pow_le_growthBound (u : K) (d : ℕ) : ‖u ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg u) ((le_max_left _ _).trans (le_max_left _ _)) d

theorem norm_inv_pow_le_growthBound (u : K) (d : ℕ) : ‖u⁻¹ ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((le_max_right _ _).trans (le_max_left _ _)) d

theorem one_le_growthBound_pow (u : K) (d : ℕ) : (1 : ℝ) ≤ growthBound u ^ d :=
  one_le_pow₀ (one_le_growthBound u)

theorem norm_natCast_le_growthBound_pow (u : K) (k d : ℕ) :
    ‖(k : K)‖ ≤ growthBound u ^ d :=
  (IsUltrametricDist.norm_natCast_le_one K k).trans (one_le_growthBound_pow u d)

theorem norm_xDivTerm_le (u : K) (d : ℕ) : ‖xDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [xDivTerm]
  calc ‖(d : K) * (u ^ d + u⁻¹ ^ d - 2)‖
      = ‖(d : K)‖ * ‖u ^ d + u⁻¹ ^ d - 2‖ := norm_mul _ _
    _ ≤ 1 * ‖u ^ d + u⁻¹ ^ d - 2‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K d)
          (norm_nonneg _)
    _ = ‖u ^ d + (u⁻¹ ^ d - 2)‖ := by rw [one_mul, add_sub_assoc]
    _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d - 2‖ := norm_add_le_max' _ _
    _ ≤ growthBound u ^ d := by
        refine max_le (norm_pow_le_growthBound u d) ?_
        refine (norm_sub_le_max' _ _).trans
          (max_le (norm_inv_pow_le_growthBound u d) ?_)
        calc ‖(2 : K)‖ = ‖((2 : ℕ) : K)‖ := by norm_num
          _ ≤ growthBound u ^ d := norm_natCast_le_growthBound_pow u 2 d

theorem norm_yDivTerm_le (u : K) (d : ℕ) : ‖yDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [yDivTerm]
  refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
  · refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · calc ‖((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d)‖
          = ‖((d.choose 2 : ℕ) : K)‖ * ‖u ^ d - u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * ‖u ^ d - u⁻¹ ^ d‖ :=
            mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
              (norm_nonneg _)
        _ = ‖u ^ d - u⁻¹ ^ d‖ := one_mul _
        _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d‖ := norm_sub_le_max' _ _
        _ ≤ growthBound u ^ d := max_le (norm_pow_le_growthBound u d)
            (norm_inv_pow_le_growthBound u d)
    · calc ‖(d : K) * u⁻¹ ^ d‖ = ‖(d : K)‖ * ‖u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * (growthBound u ^ d) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one K d)
              (norm_inv_pow_le_growthBound u d) (norm_nonneg _) zero_le_one
        _ = growthBound u ^ d := one_mul _
  · exact norm_natCast_le_growthBound_pow u d d

end Coefficients

end TateCurve
