/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep (git blob c0dc5457497bc943b7be3f1b021d1663d3abd49f, sha256 8371f5e4c425ec5fce0cd336850b77243422ec845f17562f882dedf94cc09a7b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep

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

theorem AutomorphicForm.CuspidalSpectrum.finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYK : Y ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hYM : ∀ ψ ∈ Y, ∃ h : ψ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, h⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥Y := by
  revert F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ α β Φ₀ hΦ₀ M hM U hU O hO hUO tys Y hYK hYM hYU hYt
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_finiteDimensional_of_le_cuspKFiniteSubmodule_of_toCuspSubcarrier_mem_of_isIrreducibleCuspSubrep.solution
