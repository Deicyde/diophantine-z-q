/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le (git blob 9ca30759271e08210ca0b8f59efa444a0076c5e2, sha256 1a6b936aa7d7321cec6f251835390990ee7c7fb6da243801be896e9ae3575d85).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_rightConv_le
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ),
        ∃ hφg : rightConv F φ g ∈ memberSubmodule F Φ₀ ξ,
          ‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ ≤ C * ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩‖ := by
  revert F α β Φ₀ hΦ₀ σ ξ hσ g hg hgc
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le.solution
