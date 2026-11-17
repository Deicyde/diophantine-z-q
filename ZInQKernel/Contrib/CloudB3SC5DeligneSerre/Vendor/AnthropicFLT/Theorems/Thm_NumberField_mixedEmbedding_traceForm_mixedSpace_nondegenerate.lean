/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate (git blob 6f3f0ab14480c700f76f2526f6425ab77eb38486, sha256 b194fb30069eb204fc3747ee74ac8fd5cddfd00dc52bb4cfa8ba8cc12fd0c2c3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped Classical
theorem NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by
  revert K
  exact @_root_.P2MW.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate.solution
