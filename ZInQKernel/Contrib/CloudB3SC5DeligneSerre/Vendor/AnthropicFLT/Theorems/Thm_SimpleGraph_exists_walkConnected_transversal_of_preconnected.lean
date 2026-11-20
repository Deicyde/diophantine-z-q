/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected (git blob bcbff63c6cb2b0e57549e825d4cec6119a54e6af, sha256 2c4d3b3497610792df3362c8cf18403face5a739072d9ad36449ec75d32fbcd9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_SimpleGraph_exists_walkConnected_transversal_of_preconnected

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem SimpleGraph.exists_walkConnected_transversal_of_preconnected {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧
      (∀ v ∈ D, ∀ w ∈ D, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ D) ∧
      (∀ v ∈ D, ∀ w ∈ D, v ∈ MulAction.orbit Γ w → v = w) ∧
      (∀ u : V, ∃ v ∈ D, v ∈ MulAction.orbit Γ u) := by
  revert V T Γ hsmul hpre v₀
  exact @_root_.P2MW.S_SimpleGraph_exists_walkConnected_transversal_of_preconnected.solution
