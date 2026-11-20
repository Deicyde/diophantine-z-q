/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_mixedEmbedding_trace_mixedEmbedding (git blob 24f7d7209cc38175cf5dca2a2d781dc1f390ce00, sha256 1978a5d1021d729578fce3c3ade07ab4ab11a76145975a6148c7245523326032).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_mixedEmbedding_trace_mixedEmbedding

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding Module
open scoped Classical

theorem solution
    (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  rw [Algebra.trace_eq_matrix_trace (latticeBasis K) (mixedEmbedding K x),
    Algebra.trace_eq_matrix_trace (integralBasis K) x, Matrix.trace, Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, latticeBasis_apply, ← map_mul, latticeBasis_repr_apply]
