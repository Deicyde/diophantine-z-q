/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_linearMap_archCutProjector (git blob 3109b4975dd109f3df5376845df568dbca3bb830, sha256 56c0cb04f8a0ea31230bed0f1c543de020c83880a8f1398f353752fefa2bff4d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_rightConv_eq_of_archCutProjector

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_linearMap_archCutProjector

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) :
    ∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) ∧
      (∀ y : AdelicGL2 (𝓞 F) F → ℂ, Continuous y → y ∈ archCutSubmodule F tys →
        ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys' : ArchTypeFamily F), IsFactorizableTestFn F f → IsArchBiFinite F tys' f →
          ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
            Q (rightConv F y f) = rightConv F y f') := by
  obtain ⟨Q, h1, h2, h3⟩ := AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate F tys
  exact ⟨Q, h1, h2, fun y hyc hy f tys' hf hbf =>
    AutomorphicForm.exists_rightConv_eq_of_archCutProjector F tys Q ⟨h1, h2, h3⟩ hyc hy tys' hf hbf⟩
