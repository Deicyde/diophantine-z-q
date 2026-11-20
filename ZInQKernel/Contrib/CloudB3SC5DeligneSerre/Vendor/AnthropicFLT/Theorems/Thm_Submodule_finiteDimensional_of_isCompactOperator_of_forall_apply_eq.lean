/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq (git blob 4ef3cdd1fc3dc69c431db03df16c2c7187308894, sha256 cb1b2a25a39c24299ea41e02e5c2f55d1147564a57093583409dfc4f3b25277b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open Topology

theorem Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (V : Submodule 𝕜 E) (hV : ∀ v ∈ V, T v = v) :
    FiniteDimensional 𝕜 ↥V := by
  revert 𝕜 E T hT V hV
  exact @_root_.P2MW.S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq.solution
