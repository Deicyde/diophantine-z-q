import ZInQKernel.Contrib.OneProof.CMHeight62.Archimedean
import ZInQKernel.Contrib.OneProof.CMHeight62.Model
import ZInQKernel.Contrib.OneProof.CMHeight62.ShortModel
import ZInQKernel.Contrib.OneProof.CMBranch

/-! # cmheight62-p1: the exact height formula, the finite-place step 7, and `CMHeight62`

* `ArchIdentity` (steps 1, 2 (nonvanishing) and 4): for every smooth group model `𝒢` of `E_L`
  (no properness), every metrized model `M` on it, every short datum `D` of `E` and periods
  `τ_σ`, `η_W ≠ 0` and `|σ Δ_W| · ‖η_W‖_σ¹² = |Δ(τ_σ)| · (Im τ_σ)⁶` at every `σ : L → ℂ`.
* `finrank_mul_modelHeight_eq_exact` (step 6): from `ArchIdentity`,
  `[L:ℚ] h(𝒢) = Σ_σ summand62 τ_σ + (1/12)(log |N_{L/ℚ}(Δ_W)| − 12 log N(Jη))`.
* `Step7` (the open finite-place inequality, a named Prop, not proved here): for proper `𝒢`,
  `|N_{L/ℚ}(Δ_W)| ≤ N(Jη)¹²`.
* `cmHeight62_of_step7`: `ArchIdentity → Step7 → CMHeight62`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open NumberField AlgebraicGeometry
open ZInQ.DefFaltings
open ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal

/-- **Steps 1, 2 (nonvanishing) and 4, stated.** For an elliptic curve `E/K`, a short datum `D`
(`W = (0,0,0,a,b)` over `K`), a metrized model `M` of `E_L` (any smooth group model, no
properness) and periods `τ_σ` of `E` at `σ|_K`: `η_W ≠ 0` and, at every `σ : L → ℂ`,
`|σ(Δ_W)| · ‖η_W‖_σ¹² = |Δ(τ_σ)| · (Im τ_σ)⁶` with `Δ(τ) = (2π)¹² η(τ)²⁴`. -/
def ArchIdentity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : PkgI3.AbVar K), E.dim = 1 → ∀ (D : ShortData E) (M : MetrizedModel E L 1)
    (τ : (L →+* ℂ) → ℂ),
    (∀ σ, 0 < (τ σ).im ∧ HDec.CMBranch.IsPeriodAt E (σ.comp (algebraMap K L)) (τ σ)) →
    D.etaW M.model ≠ 0 ∧
      ∀ σ : L →+* ℂ, ‖σ (algebraMap K L D.W.Δ)‖ * M.hodge.norm σ (D.etaW M.model) ^ 12 =
        ‖CMBranch.discAn (τ σ)‖ * (τ σ).im ^ 6

/-- **Step 7 (the finite-place inequality), stated; not proved here.** For a proper smooth group
model `𝒢` of `E_L` over `𝓞_L` and any short datum `D` of `E/K`, with `η_W = 1 ⊗ d(−x/y)` and
`Jη = {a ∈ L : a • η_W ∈ ⋀¹ω_𝒢}`: `|N_{L/ℚ}(Δ_W)| ≤ N(Jη)¹²` (the `L`-norm of the image of
`Δ_W ∈ K`). Locally at a prime `𝔭` of `𝓞_L`: `v_𝔭(Δ_W) ≤ 12 v_𝔭(μ)` where `ω_𝒢 = μ·η_W`. -/
def Step7 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : PkgI3.AbVar K) (hdim : E.dim = 1) (D : ShortData E) (𝒢 : GroupModel E L),
    IsProper 𝒢.G.hom → ∀ hη : D.etaW 𝒢 ≠ 0,
      |Algebra.norm ℚ (algebraMap K L D.W.Δ)| ≤
        FractionalIdeal.absNorm (coefficientFractionalIdeal 𝒢 hdim (D.etaW 𝒢) hη) ^ 12

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  {E : PkgI3.AbVar K}

/-- **Step 6: the exact height formula, for every smooth model** (no properness), given the
archimedean identity. -/
theorem finrank_mul_modelHeight_eq_exact (hA : ArchIdentity) (hdim : E.dim = 1)
    (D : ShortData E) (M : MetrizedModel E L 1) (τ : (L →+* ℂ) → ℂ)
    (hτ : ∀ σ, 0 < (τ σ).im ∧ HDec.CMBranch.IsPeriodAt E (σ.comp (algebraMap K L)) (τ σ)) :
    ∃ hη : D.etaW M.model ≠ 0,
      (Module.finrank ℚ L : ℝ) * M.hodge.modelHeight =
        ∑ σ : L →+* ℂ, CMBranch.summand62 (τ σ) +
          (1 / 12) * (Real.log |(Algebra.norm ℚ (algebraMap K L D.W.Δ) : ℝ)| -
            12 * Real.log (FractionalIdeal.absNorm
              (coefficientFractionalIdeal M.model hdim (D.etaW M.model) hη) : ℝ)) := by
  obtain ⟨hη, harch⟩ := hA K L E hdim D M τ hτ
  refine ⟨hη, ?_⟩
  exact finrank_mul_modelHeight_eq_summand62 M hdim _ hη _
    ((map_ne_zero (algebraMap K L)).mpr D.W_Δ_ne_zero) τ harch

/-- **`CMHeight62` from the archimedean identity and step 7.** -/
theorem cmHeight62_of_step7 (hA : ArchIdentity) (h7 : Step7) : HDec.CMBranch.CMHeight62 := by
  intro K _ _ L _ _ _ E hdim 𝒢 hprop τ hτ
  let D := shortData E hdim
  obtain ⟨M, hM⟩ := exists_metrizedModel hdim 𝒢
  subst hM
  obtain ⟨hη, hform⟩ := finrank_mul_modelHeight_eq_exact hA hdim D M τ hτ
  have h7' := h7 K L E hdim D M.model hprop hη
  set J := FractionalIdeal.absNorm (coefficientFractionalIdeal M.model hdim (D.etaW M.model) hη)
  set N := Algebra.norm ℚ (algebraMap K L D.W.Δ)
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr
    ((map_ne_zero (algebraMap K L)).mpr D.W_Δ_ne_zero)
  have hNpos : (0 : ℝ) < |(N : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hN
  have hlog : Real.log |(N : ℝ)| ≤ 12 * Real.log (J : ℝ) := by
    have h1 : |(N : ℝ)| ≤ (J : ℝ) ^ 12 := by exact_mod_cast h7'
    have h2 := Real.log_le_log hNpos h1
    rwa [Real.log_pow] at h2
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hle : M.hodge.modelHeight ≤ (∑ σ : L →+* ℂ, CMBranch.summand62 (τ σ)) /
      Module.finrank ℚ L := by
    rw [le_div_iff₀ hd, mul_comm, hform]
    nlinarith
  exact (stableFaltingsHeight_le E M).trans (EReal.coe_le_coe_iff.mpr hle)

end ZInQ.Contrib.CMHeight62
