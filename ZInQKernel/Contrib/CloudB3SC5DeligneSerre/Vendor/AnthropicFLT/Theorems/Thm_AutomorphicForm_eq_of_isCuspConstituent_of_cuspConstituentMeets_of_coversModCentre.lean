/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre (git blob cbe5bb4e2182593b8fd4edd719660a173c5ffbd3, sha256 46be9683f7a49d55b3ee6d9d98874545c44606a50f20faf608a2ffddd7f01447).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ V₂)
    (m₁ : AutomorphicForm.CuspidalConstituent.CuspConstituentMeets F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N S Ψ V₁)
    (m₂ : AutomorphicForm.CuspidalConstituent.CuspConstituentMeets F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N S Ψ V₂) :
    V₁ = V₂ := by
  revert F c u d₁ d₂ T hd hcov ξ N S Ψ V₁ V₂ h₁ h₂ m₁ m₂
  exact @_root_.P2MW.S_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre.solution
