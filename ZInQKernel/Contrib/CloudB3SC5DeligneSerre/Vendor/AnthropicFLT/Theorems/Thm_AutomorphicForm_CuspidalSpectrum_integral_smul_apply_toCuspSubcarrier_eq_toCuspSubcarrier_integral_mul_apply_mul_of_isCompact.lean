/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact (git blob 676e0833089e0cc91661c92cabf138ee9ca4ffcf, sha256 a6e4f61971e2270d7803188665f7158487506ab89b210f9d557ec011182c88d3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (hUf : U ≤ finiteAdelicGL2Subgroup F)
    [MeasurableSpace ↥U] [BorelSpace ↥U] (μ : Measure ↥U) [IsFiniteMeasure μ]
    (S : ↥U → (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hS : ∀ u : ↥U, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (S u))
    (hSc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun u : ↥U => S u v)
    (c : ↥U → ℂ) (hc : Continuous c)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    ∃ h : (fun x => ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ) ∈ cuspMemberSubmodule F Φ₀ ξ,
      ∫ u, c u • S u (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂μ =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ, h⟩ := by
  revert F α β Φ₀ hΦ₀ σ ξ U hU hUf μ S hS hSc c hc φ hφ
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact.solution
