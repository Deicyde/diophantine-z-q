/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule (git blob 1219d6e5b7003052d2eae80bd3c71757ed3e77d0, sha256 310307f7688310273cf17077680fb93f0b7a0f5ec230dec2602b3326cb80bd00).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering open AutomorphicForm hiding exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (hVN : ∃ φ ∈ V, φ ≠ 0 ∧ φ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    V ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
  revert F c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN hVN c' u' d₁' d₂' T' hc' hd₁'
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule.solution
