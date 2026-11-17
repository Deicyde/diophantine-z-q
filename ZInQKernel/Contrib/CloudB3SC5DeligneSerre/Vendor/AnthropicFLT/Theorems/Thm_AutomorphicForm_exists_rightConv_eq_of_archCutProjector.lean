/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_rightConv_eq_of_archCutProjector (git blob cf39c001eea33caee143164ab8d67d5bb4423bf9, sha256 06b4ecd6a23e6acd1e4d74f43eea630b39ba558cf89b2b6c6cb1239a8c39a879).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.exists_rightConv_eq_of_archCutProjector
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (hQ :
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ)))
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hy : y ∈ archCutSubmodule F tys)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (tys' : ArchTypeFamily F) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys' f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧ Q (rightConv F y f) = rightConv F y f' := by
  revert F tys Q hQ y hyc hy f tys' hf hbf
  exact @_root_.P2MW.S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector.solution
