/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero (git blob f323efd6ee3143734039f2f15ab72765e07a671a, sha256 95efb214a2d941b539640706a9fd33f3c23a621aad05076bcba7183a991ca03d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : v ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ),
      IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧ flat F σ f = f ∧
      ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCompactOperator Tc ∧ (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric ∧
        IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc ∧ Tc v ≠ 0 := by
  obtain ⟨tys, U, hUf, hUo, hUc, hUi, ψ, hψ, hψt, hψU, hinner⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero F hΦ₀ σ ξ hσ v hv
  set a : ℂ := ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ with ha
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr hinner
  set ε : ℝ := ‖a‖ / (‖v‖ + 1) with hεdef
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hε : 0 < ε := div_pos ha0 hv1
  obtain ⟨f, hft, hsph, hflat, hψf, hclose⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
      F hΦ₀ σ ξ hσ U hUf hUo hUc hUi tys ψ hψ hψU hψt ε hε
  obtain ⟨fa, -, hfa_bf, -, hfa_eq⟩ := hsph
  have hfbf : IsArchBiFinite F tys f := IsArchBiFinite.of_factorization F hfa_eq hfa_bf
  obtain ⟨Tc, hcpt, hsymm, hlift⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv F hΦ₀ σ ξ hσ f hft hflat
  refine ⟨tys, f, hft, hfbf, hflat, Tc, hcpt, hsymm, hlift, ?_⟩

  intro h0
  have h1 : ⟪Tc v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ = ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ := by
    rw [← hlift ⟨ψ, hψ⟩ hψf]
    exact hsymm v _
  rw [h0, inner_zero_left] at h1

  have h2 : ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ =
      a - ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ := by
    rw [inner_sub_right, ha]; ring
  have h3 : ‖⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ‖ < ‖a‖ := by
    calc _ ≤ ‖v‖ * ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * ε := mul_le_mul_of_nonneg_left hclose.le (norm_nonneg _)
      _ < ‖a‖ := by
          rw [hεdef, mul_div_assoc']
          rw [div_lt_iff₀ hv1]
          nlinarith [norm_nonneg v]
  have h4 : ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ ≠ 0 := by
    rw [h2]
    intro hz
    rw [sub_eq_zero] at hz
    rw [← hz] at h3
    exact lt_irrefl _ h3
  exact h4 h1.symm
