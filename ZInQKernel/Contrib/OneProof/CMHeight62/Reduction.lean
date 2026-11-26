import ZInQKernel.Contrib.OneProof.CMHeight62.Metrization

/-! # cmHeight62, step 3: the reduction

`cmHeight62_of_print`: `CMHeight62` follows from the print row `NTProp1` and the glue
`MetrizationExists62` (itself assembled from three named parts in `Metrization.lean`). The proof
takes the metrization `M` of the given model, reads its height off the print
(`modelHeight_eq_of_print`: `h_F = [L:ℚ]⁻¹ ∑_σ summand62 τ_σ` once Deligne's `(1/2) log π` is
removed) and bounds the stable height by it (`stableFaltingsHeight_le`).
-/

namespace HDec
namespace CMBranch
namespace H62

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ.DefFaltings
open _root_.CMBranch

theorem discAn_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : discAn τ ≠ 0 := by
  unfold discAn
  have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  exact mul_ne_zero (pow_ne_zero _ h2π) (pow_ne_zero _ (ModularForm.eta_ne_zero hτ))

/-- The log of one factor of the print: `log((Im τ/π)^{1/2} |Δ(τ)|^{1/12})
= −summand62 τ − (1/2) log π`. -/
theorem log_factor {τ : ℂ} (hτ : 0 < τ.im) :
    Real.log (((τ.im / Real.pi) ^ (1 / 2 : ℝ)) * ‖discAn τ‖ ^ (1 / 12 : ℝ)) =
      -summand62 τ - 1 / 2 * Real.log Real.pi := by
  have hΔ : 0 < ‖discAn τ‖ := norm_pos_iff.mpr (discAn_ne_zero hτ)
  have hq : 0 < τ.im / Real.pi := div_pos hτ Real.pi_pos
  rw [Real.log_mul (Real.rpow_pos_of_pos hq _).ne' (Real.rpow_pos_of_pos hΔ _).ne',
    Real.log_rpow hq, Real.log_rpow hΔ, Real.log_div hτ.ne' Real.pi_pos.ne', summand62,
    Real.log_mul hΔ.ne' (pow_pos hτ 6).ne', Real.log_pow]
  push_cast
  ring

/-- **The height from the print** (proved): if `exp(−d (h + (1/2) log π))` is the print's
product, then `h = d⁻¹ ∑_σ summand62 τ_σ`. -/
theorem modelHeight_eq_of_print {L : Type} [Field L] [NumberField L] (h : ℝ)
    (τ : (L →+* ℂ) → ℂ) (hτ : ∀ σ, 0 < (τ σ).im)
    (hP : Real.exp (-(Module.finrank ℚ L : ℝ) * (h + 1 / 2 * Real.log Real.pi)) =
      ∏ σ, ((τ σ).im / Real.pi) ^ (1 / 2 : ℝ) * ‖discAn (τ σ)‖ ^ (1 / 12 : ℝ)) :
    h = (∑ σ, summand62 (τ σ)) / Module.finrank ℚ L := by
  have hpos : ∀ σ, 0 < ((τ σ).im / Real.pi) ^ (1 / 2 : ℝ) * ‖discAn (τ σ)‖ ^ (1 / 12 : ℝ) :=
    fun σ => mul_pos (Real.rpow_pos_of_pos (div_pos (hτ σ) Real.pi_pos) _)
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (discAn_ne_zero (hτ σ))) _)
  have hlog := congrArg Real.log hP
  rw [Real.log_exp, Real.log_prod (fun σ _ => (hpos σ).ne')] at hlog
  simp only [fun σ => log_factor (hτ σ)] at hlog
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card L ℂ, nsmul_eq_mul] at hlog
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  rw [eq_div_iff hn.ne']
  linarith

/-- **The reduction** (proved): `CMHeight62` from the print row and the metrization glue. -/
theorem cmHeight62_of_print (hP : NTProp1) (hM : MetrizationExists62) : CMHeight62 := by
  intro K _ _ L _ _ _ E hE 𝒢 h𝒢 τ hτ
  obtain ⟨M, hM𝒢⟩ := hM K L E hE 𝒢 h𝒢 τ hτ
  have hh := modelHeight_eq_of_print M.hodge.modelHeight τ (fun σ => (hτ σ).1)
    (hP K L E hE 𝒢 h𝒢 M hM𝒢 τ hτ)
  calc stableFaltingsHeight E ≤ (M.hodge.modelHeight : EReal) := stableFaltingsHeight_le E M
    _ = _ := by rw [hh]

/-- **The reduction through the three glue parts** (proved). -/
theorem cmHeight62_of_parts (hP : NTProp1) (hH : HodgeLine62) (hU : UnifTransfer62)
    (hC : CoeffMap62) : CMHeight62 :=
  cmHeight62_of_print hP (metrizationExists62_of hH hU hC)

end H62
end CMBranch
end HDec
