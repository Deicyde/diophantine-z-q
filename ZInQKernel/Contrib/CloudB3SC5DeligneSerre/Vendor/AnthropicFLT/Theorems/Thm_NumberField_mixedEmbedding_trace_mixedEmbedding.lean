/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding (git blob 85178a1ea31ed18f3bac0235a2652a4b3f3c6fc6, sha256 b39a4948e93568c09ae64c72b4034e013ec841b7abd49c5f56c63e893e5c4f6d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_mixedEmbedding_trace_mixedEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped Classical
theorem NumberField.mixedEmbedding.trace_mixedEmbedding
    (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  revert K x
  exact @_root_.P2MW.S_NumberField_mixedEmbedding_trace_mixedEmbedding.solution
