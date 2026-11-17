/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn (git blob f59fc8a95b20dff8096ff7ba494f413895d56442, sha256 f8182aa140092685b2f5352bd49af15c9056b60387af2134aa39f50232f3b4c7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain
theorem AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f := by
  revert F f hf
  exact @_root_.P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn.solution
