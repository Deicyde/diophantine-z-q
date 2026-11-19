/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent (git blob 8277d32c57e38ad15a690d0210eb0a28db332054, sha256 8f16e5aa7b96cf6ca30b06d95537aa34a8869df064746f570c31be8679158a1a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by
  revert κ k n f hf
  exact @_root_.P2MW.S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.solution
