import ZInQKernel.HDecomp.Faltings.Height
import ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.Fractional
import ZInQKernel.Contrib.OneProof.CMBranch.Arith

/-! # cmheight62-p1: the height of a metrized model of an elliptic curve in any coordinate

Steps 3, 5 and 6 (abstract form) of the cmHeight62 route, over an arbitrary
`MetrizedModel E L 1` with `E.dim = 1`. No properness, no CM, no reduced period.

* `finrank_mul_modelHeight_eq` (step 3): for every nonzero `η` in the Hodge line (not necessarily
  in the lattice), with `Jη = {a : a • η ∈ ⋀¹ω_𝒢}` (`coefficientFractionalIdeal`, so
  `⋀¹ω_𝒢 = Jη · η`),
  `[L:ℚ] · h(𝒢) = −log N(Jη) − Σ_σ log ‖η‖_σ`.
* `finrank_mul_modelHeight_eq_summand62` (steps 5-6, abstract): if `D ∈ L` and periods `τ_σ`
  satisfy `|σ D| · ‖η‖_σ¹² = |Δ(τ_σ)| · (Im τ_σ)⁶` at every `σ`, then
  `[L:ℚ] · h(𝒢) = Σ_σ summand62 τ_σ + (1/12)(log |N_{L/ℚ} D| − 12 log N(Jη))`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open NumberField
open ZInQ.DefFaltings
open ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- A nonzero fractional ideal has a nonzero element. -/
theorem exists_mem_coefficientFractionalIdeal_ne_zero (G : GroupModel E L) (hdim : E.dim = 1)
    (η : G.hodgeSpace 1) (hη : η ≠ 0) :
    ∃ a : L, a ∈ coefficientSubmodule (G.detLattice 1) η ∧ a ≠ 0 := by
  have h := coefficientFractionalIdeal_ne_zero G hdim η hη
  rw [Ne, ← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_zero,
    coefficientFractionalIdeal_coe, Submodule.eq_bot_iff] at h
  push Not at h
  exact h

/-- **Step 3.** `[L:ℚ] · h(𝒢) = −log N(Jη) − Σ_σ log ‖η‖_σ` for every nonzero `η` in the Hodge
line of a metrized model of an elliptic curve, `Jη` the coefficient fractional ideal of the
Hodge lattice in the coordinate `η` (`⋀¹ω_𝒢 = Jη · η`). -/
theorem finrank_mul_modelHeight_eq (M : MetrizedModel E L 1) (hdim : E.dim = 1)
    (η : M.model.hodgeSpace 1) (hη : η ≠ 0) :
    (Module.finrank ℚ L : ℝ) * M.hodge.modelHeight =
      -Real.log (FractionalIdeal.absNorm (coefficientFractionalIdeal M.model hdim η hη) : ℝ) -
        ∑ σ : L →+* ℂ, Real.log (M.hodge.norm σ η) := by
  obtain ⟨a, ha, ha0⟩ := exists_mem_coefficientFractionalIdeal_ne_zero M.model hdim η hη
  have hmem : a • η ∈ M.hodge.lattice := by rw [M.lattice_eq]; exact ha
  have hne : a • η ≠ 0 := smul_ne_zero ha0 hη
  have hd : (Module.finrank ℚ L : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := L)
    exact_mod_cast this.ne'
  have hidx := secIndex_detLattice_eq_norm_div M.model hdim η hη ha ha0
  set J := coefficientFractionalIdeal M.model hdim η hη
  have hJ : (FractionalIdeal.absNorm J : ℝ) ≠ 0 := by
    exact_mod_cast coefficientFractionalIdeal_absNorm_ne_zero M.model hdim η hη
  have hJpos : (0 : ℝ) < FractionalIdeal.absNorm J := by
    have : (0 : ℚ) ≤ FractionalIdeal.absNorm J := FractionalIdeal.absNorm_nonneg J
    exact lt_of_le_of_ne (by exact_mod_cast this) (Ne.symm hJ)
  have hNa : (|Algebra.norm ℚ a| : ℝ) ≠ 0 := by
    have : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha0
    exact_mod_cast abs_ne_zero.mpr this
  have hidxR : ((secIndex M.hodge.lattice (a • η) : ℕ) : ℝ) =
      |(Algebra.norm ℚ a : ℝ)| / (FractionalIdeal.absNorm J : ℝ) := by
    rw [M.lattice_eq]
    have := congrArg (fun q : ℚ => (q : ℝ)) hidx
    simpa using this
  have hnorm : ∀ σ : L →+* ℂ, Real.log (M.hodge.norm σ (a • η)) =
      Real.log ‖σ a‖ + Real.log (M.hodge.norm σ η) := by
    intro σ
    have h1 : M.hodge.norm σ (a • η) = ‖σ a‖ * M.hodge.norm σ η :=
      M.hodge.hodgeBundle.norm_smul σ a η
    rw [h1, Real.log_mul (by simpa using ha0) (show 0 < M.hodge.norm σ η from M.hodge.hodgeBundle.norm_pos σ η hη).ne']
  have hdeg : M.hodge.hodgeBundle.arakelovDegree = M.hodge.hodgeBundle.degreeAt (a • η) :=
    (M.hodge.hodgeBundle.degreeAt_eq_arakelovDegree hmem hne).symm
  rw [HodgeData.modelHeight, mul_div_cancel₀ _ hd, hdeg]
  unfold HermitianLattice.degreeAt
  change Real.log ((secIndex M.hodge.lattice (a • η) : ℕ) : ℝ) -
      ∑ σ : L →+* ℂ, Real.log (M.hodge.norm σ (a • η)) = _
  rw [hidxR, Finset.sum_congr rfl (fun σ _ => hnorm σ), Finset.sum_add_distrib,
    sum_log_norm_embeddings a ha0, Real.log_div (by simpa using hNa) hJ]
  ring

/-- **Product formula, used in step 5.** `Σ_σ log |σ D| = log |N_{L/ℚ} D|`. -/
theorem sum_log_norm_eq (D : L) (hD : D ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ D‖ = Real.log |(Algebra.norm ℚ D : ℝ)| :=
  sum_log_norm_embeddings D hD

/-- **Steps 5-6, abstract form.** If at every `σ` the archimedean identity
`|σ D| · ‖η‖_σ¹² = |Δ(τ_σ)| · (Im τ_σ)⁶` holds, then
`[L:ℚ] · h(𝒢) = Σ_σ summand62 τ_σ + (1/12)(log |N_{L/ℚ} D| − 12 log N(Jη))`. -/
theorem finrank_mul_modelHeight_eq_summand62 (M : MetrizedModel E L 1) (hdim : E.dim = 1)
    (η : M.model.hodgeSpace 1) (hη : η ≠ 0) (D : L) (hD : D ≠ 0) (τ : (L →+* ℂ) → ℂ)
    (harch : ∀ σ, ‖σ D‖ * M.hodge.norm σ η ^ 12 =
      ‖CMBranch.discAn (τ σ)‖ * (τ σ).im ^ 6) :
    (Module.finrank ℚ L : ℝ) * M.hodge.modelHeight =
      ∑ σ : L →+* ℂ, CMBranch.summand62 (τ σ) +
        (1 / 12) * (Real.log |(Algebra.norm ℚ D : ℝ)| -
          12 * Real.log (FractionalIdeal.absNorm
            (coefficientFractionalIdeal M.model hdim η hη) : ℝ)) := by
  rw [finrank_mul_modelHeight_eq M hdim η hη, ← sum_log_norm_eq D hD]
  have hσ : ∀ σ : L →+* ℂ, Real.log (M.hodge.norm σ η) =
      -CMBranch.summand62 (τ σ) - (1 / 12) * Real.log ‖σ D‖ := by
    intro σ
    have hpos : 0 < M.hodge.norm σ η := M.hodge.hodgeBundle.norm_pos σ η hη
    have hDσ : ‖σ D‖ ≠ 0 := by simpa using hD
    unfold CMBranch.summand62
    rw [← harch σ, Real.log_mul hDσ (pow_ne_zero _ hpos.ne'), Real.log_pow]
    change Real.log (M.hodge.norm σ η) = _
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun σ _ => hσ σ), Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  ring

end ZInQ.Contrib.CMHeight62
