/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate (git blob c2419b5ab1ae0dc66c77ed90b3fbd5fe9a40241d, sha256 18865392783137b069e6c88b533203d68cf561224910930836902d9de9f9d870).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding Module
open scoped Classical

theorem solution
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ (latticeBasis K)
  have h : LinearMap.BilinForm.toMatrix (latticeBasis K) (Algebra.traceForm ℝ (mixedSpace K))
      = (Algebra.traceMatrix ℚ (integralBasis K)).map (algebraMap ℚ ℝ) := by
    ext i j
    rw [Algebra.traceForm_toMatrix, Matrix.map_apply, Algebra.traceMatrix_apply,
      latticeBasis_apply, latticeBasis_apply, ← map_mul, NumberField.mixedEmbedding.trace_mixedEmbedding,
      Algebra.traceForm_apply, eq_ratCast]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Algebra.discr_def, map_ne_zero]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)
