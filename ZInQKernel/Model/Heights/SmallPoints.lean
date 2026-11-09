import ZInQKernel.Model.Heights.Canonical
import ZInQKernel.Model.Heights.Comparisons

/-!
# The height of `2R` and multiples of small points

Blueprint: `model/heights/height-of-2r.md`, `model/heights/small-height-bound.md`.

`h_x([2]R) = h((57 - 28 s)/8) = log 41`, from `57² - 2·28² = 41²`, `49² > 2·28²` and `57` odd.
Consequently `ĥ(R) > 0`, and if `R = [m]S + T` with `T ∈ C(K₀)[2]` and `|m| ≥ 3`, then
`h_x(S) ≤ log(41³·676)/108 + log 392/3 < log 9`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-- The three closed integer facts behind `h_x([2]R) = log 41`. -/
theorem height_two_R_integer_facts :
    (57 : ℤ) ^ 2 - 2 * 28 ^ 2 = 41 ^ 2 ∧ 2 * 28 ^ 2 < (49 : ℤ) ^ 2 ∧ (57 : ℤ) % 2 = 1 := by
  decide

/-- `x([2]R) = (57 - 28 s) / 8` as a fraction in `ℤ[s]`. -/
theorem twoRX_eq_div : twoRX = Zs.toK0 ⟨57, -28⟩ / Zs.toK0 8 := by
  rw [map_ofNat, eq_div_iff (by norm_num)]
  ext <;> norm_num [twoRX]

/-- `57 - 28 s` and `8 = s⁶` are coprime: `(57 + 28 s)(57 - 28 s) - 210 · 8 = 1`. -/
theorem isCoprime_twoR : IsCoprime (⟨57, -28⟩ : Zs) 8 :=
  ⟨⟨57, 28⟩, -210, by decide⟩

/-- `s ∤ 57 - 28 s` since `57` is odd. -/
theorem not_sqrt2Z_dvd_twoR : ¬ sqrt2Z ∣ (⟨57, -28⟩ : Zs) := by
  rw [sqrt2Z_dvd_iff]; decide

/-- **The height of `2R`**: `h_x([2]R) = log 41`. -/
theorem hx_two_R : hx (2 • pointR) = Real.log 41 := by
  obtain ⟨hn, hlt, -⟩ := height_two_R_integer_facts
  rw [two_smul_pointR, hx_some, twoRX_eq_div, hK0_div_of_isCoprime isCoprime_twoR]
  simp only [map_ofNat]
  rw [K0.embPlus_apply, K0.embMinus_apply]
  simp only [Zs.toK0_re, Zs.toK0_im]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have h28 : (28 : ℝ) * Real.sqrt 2 < 49 := by
    have : ((2 * 28 ^ 2 : ℤ) : ℝ) < ((49 ^ 2 : ℤ) : ℝ) := by exact_mod_cast hlt
    push_cast at this
    nlinarith
  have e1 : (((57 : ℤ) : ℚ) : ℝ) + (((-28 : ℤ) : ℚ) : ℝ) * Real.sqrt 2 = 57 - 28 * Real.sqrt 2 := by
    push_cast; ring
  have e2 : (((57 : ℤ) : ℚ) : ℝ) - (((-28 : ℤ) : ℚ) : ℝ) * Real.sqrt 2 = 57 + 28 * Real.sqrt 2 := by
    push_cast; ring
  have hp : (8 : ℝ) < 57 - 28 * Real.sqrt 2 := by linarith
  have hm : (8 : ℝ) < 57 + 28 * Real.sqrt 2 := by linarith
  have hp0 : (0 : ℝ) < 57 - 28 * Real.sqrt 2 := by linarith
  have hm0 : (0 : ℝ) < 57 + 28 * Real.sqrt 2 := by linarith
  rw [e1, e2, abs_of_pos hp0, abs_of_pos hm0, abs_of_pos (by norm_num : (0 : ℝ) < 8),
    max_eq_left hp.le, max_eq_left hm.le, ← Real.log_mul hp0.ne' hm0.ne']
  have : ((57 : ℝ) - 28 * Real.sqrt 2) * (57 + 28 * Real.sqrt 2) = 41 ^ 2 := by
    have : (((57 : ℤ) ^ 2 - 2 * 28 ^ 2 : ℤ) : ℝ) = ((41 ^ 2 : ℤ) : ℝ) := by exact_mod_cast hn
    push_cast at this
    nlinarith
  rw [this, Real.log_pow]; push_cast; ring

/-- **A multiple of a small point (1)**: `8 ĥ(R) = 2 ĥ([2]R) ≥ log 41 - log 392 / 3 > 0`. -/
theorem canonHeight_R_pos :
    8 * canonHeight pointR = 2 * canonHeight (2 • pointR) ∧
      Real.log 41 - Real.log 392 / 3 ≤ 2 * canonHeight (2 • pointR) ∧
      0 < Real.log 41 - Real.log 392 / 3 ∧ 0 < canonHeight pointR := by
  have h1 := hx_le_two_canonHeight (2 • pointR)
  rw [hx_two_R] at h1
  have h2 := canonHeight_two_smul pointR
  have h3 := log_height_comparison_two
  refine ⟨by rw [h2]; ring, by linarith, by linarith, by linarith⟩

/-- **A multiple of a small point (2)**: if `R = [m]S + T` with `T ∈ C(K₀)[2]` and `|m| ≥ 3`, then
`h_x(S) ≤ log(41³·676)/108 + log 392/3 < log 9`. -/
theorem hx_lt_log_nine_of_multiple (S T : curveC.toAffine.Point) (m : ℤ)
    (hR : pointR = m • S + T) (hT : 2 • T = 0) (hm : 3 ≤ |m|) :
    hx S ≤ Real.log (41 ^ 3 * 676) / 108 + Real.log 392 / 3 ∧ hx S < Real.log 9 := by
  have hRS : canonHeight pointR = (m : ℝ) ^ 2 * canonHeight S := by
    rw [hR, canonHeight_add_twoTorsion _ _ hT, canonHeight_zsmul]
  have h2R := two_canonHeight_le (2 • pointR)
  rw [hx_two_R, canonHeight_two_smul] at h2R
  have hm2 : (9 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (3 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hm
    nlinarith [sq_abs (m : ℝ), abs_nonneg (m : ℝ)]
  have hS0 := canonHeight_nonneg S
  have hlog : Real.log (41 ^ 3 * 676) = 3 * Real.log 41 + Real.log 676 := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have hS : 2 * canonHeight S ≤ Real.log (41 ^ 3 * 676) / 108 := by
    rw [hlog]
    rw [hRS] at h2R
    nlinarith
  have hxS := hx_le_two_canonHeight S
  have hc := log_height_comparison_one
  exact ⟨by linarith, by linarith⟩

end ZInQ
