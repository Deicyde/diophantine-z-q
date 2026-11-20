/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt (git blob 0f4a56ab772d5744bb3ecfd88a82fdc798256b3e, sha256 c4358d3b2c6b77155b95bf2005d53ef00ad210cba56ab7f3d37702d90365406a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt

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

open scoped Topology

theorem AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ contMemberSubmodule F Φ₀ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ y ∈ V, ∃ hy : rightTranslate F y x ∈ contMemberSubmodule F Φ₀ ξ,
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F y x, hy.1⟩ - toCarrier F hΦ₀ σ ξ ⟨x, hx.1⟩‖ < ε := by
  revert F α β Φ₀ hΦ₀ σ ξ hσ x hx ε hε
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt.solution
