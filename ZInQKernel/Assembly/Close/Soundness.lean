import ZInQKernel.Assembly.Close.Relation
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Soundness of Close

Blueprint: `assembly/approximation/close-soundness.md`.

If `Rel_close(ι(n), ι(κ), t)`, then `n ∉ 𝒞`, `κ ≠ 0` and `|t - n| < e^{-𝓑(n, κ)}` in `ℝ`, where
`𝓑(n, κ) = bound n κ = A⁽⁰⁾ |κ F(n)|²⁴` is the precision height constant
(`= H₆(S_ht) |κ F(n)|²⁴` by `Compiler.Precision.bound_eq_heightH6`). The proof is the triangle
inequality `|t - n| < 2 ε_l < 4^{-𝓑}/2 < e^{-𝓑}`; the constant `𝓑` is never evaluated.
-/

namespace ZInQ.Assembly

open Syntax Translation Compiler.Precision

/-- `e^B ≤ 4^B` for every natural `B`. -/
theorem exp_natCast_le_four_pow (B : ℕ) : Real.exp B ≤ (4 : ℝ) ^ B := by
  rw [← mul_one (B : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le
    (Real.exp_one_lt_d9.le.trans (by norm_num)) B

/-- From the closeness, precision and window tests: `|t - n| < e^{-B}`. -/
theorem abs_sub_lt_exp_of_tests {t r n eps : ℚ} {B : ℕ} (hclose : |r - n| < eps)
    (hprec : 4 * eps * 4 ^ B < 1) (hw : |t - r| < eps) :
    |(t : ℝ) - n| < Real.exp (-(B : ℝ)) := by
  have h2 : |t - n| < 2 * eps := by
    calc |t - n| = |(t - r) + (r - n)| := by ring_nf
      _ ≤ |t - r| + |r - n| := abs_add_le _ _
      _ < 2 * eps := by linarith
  have h2' : |(t : ℝ) - n| < 2 * (eps : ℝ) := by exact_mod_cast h2
  have hprec' : 4 * (eps : ℝ) * 4 ^ B < 1 := by exact_mod_cast hprec
  have h4 : (0 : ℝ) < 4 ^ B := by positivity
  have he : Real.exp (-(B : ℝ)) = (Real.exp B)⁻¹ := Real.exp_neg _
  have hle : ((4 : ℝ) ^ B)⁻¹ ≤ (Real.exp B)⁻¹ :=
    inv_anti₀ (Real.exp_pos _) (exp_natCast_le_four_pow B)
  have heps : (0 : ℝ) < eps := by
    have : (0 : ℚ) < eps := (abs_nonneg _).trans_lt hclose
    exact_mod_cast this
  have hlt : 2 * (eps : ℝ) < ((4 : ℝ) ^ B)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ h4]
    nlinarith [mul_pos heps h4]
  rw [he]
  linarith

/-- **Soundness of Close.** Under M, if `Rel_close(ι(n), ι(κ), t)`, then `n ∉ 𝒞`, `κ ≠ 0` and
`|t - n| < e^{-𝓑(n, κ)}` in `ℝ`. -/
theorem close_sound
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value)
    (n κ : ℤ) (t : ℚ)
    (h : ValRel (getEx closeSpecLib 2) (List.ofFn (iota n) ++ (List.ofFn (iota κ) ++ [t]))) :
    (n : ℚ) ∉ contactSet ∧ κ ≠ 0 ∧ |(t : ℝ) - n| < Real.exp (-(bound n κ : ℝ)) := by
  obtain ⟨n', κ', a, l, hn, hκ, hacc, hw⟩ := (close_relation_iff hM _ _ t).1 h
  obtain rfl := iota_injective hn
  obtain rfl := iota_injective hκ
  obtain ⟨⟨hnC, hκ0, -⟩, -, hclose, hprec⟩ := (accepts_enc_iff _ _ _ _ _).1 hacc
  refine ⟨(cast_mem_contactSet_iff n).not.2 hnC, hκ0, ?_⟩
  exact abs_sub_lt_exp_of_tests hclose hprec hw

end ZInQ.Assembly
