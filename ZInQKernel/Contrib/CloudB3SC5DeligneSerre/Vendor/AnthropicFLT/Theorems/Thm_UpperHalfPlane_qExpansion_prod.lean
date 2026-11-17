/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_qExpansion_prod (git blob ecf2a09c24f7bd7da6a9af51154a5c3b47389d51, sha256 11f758c44d3aaf8b4dfeb0dd4d55854c131754341ab1fe023e08025b2bdea5b5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_qExpansion_prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped Manifold
theorem UpperHalfPlane.qExpansion_prod {h : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (F i)) 0) : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) := by
  revert h ι s F hF
  exact @_root_.P2MW.S_UpperHalfPlane_qExpansion_prod.solution
