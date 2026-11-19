/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule (git blob f8b76856d7408f98846f367a731ee6894f767152, sha256 a9f80c0b1193d096f61431557051c443fcc387bbf2d2ec43da6000994b99793c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicBox AutomorphicForm AutomorphicForm.CuspidalConstituent IsDedekindDomain

theorem AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (productionPinsOf K D U gen (adelicBox K)).Z →* ℂˣ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ cuspKFiniteSubmodule K (productionPinsOf K D U gen (adelicBox K)) ξ) :
    Continuous x ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      IsSmoothCuspAutomorphicFnAt K (productionPinsOf K D U gen (adelicBox K)) ξ (rightTranslate K g x) := by
  revert K D U gen ξ x hx
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule.solution
