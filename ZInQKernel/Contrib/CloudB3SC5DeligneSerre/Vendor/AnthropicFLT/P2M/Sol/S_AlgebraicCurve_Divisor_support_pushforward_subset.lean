/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_support_pushforward_subset (git blob 49542f1071575f2e695f5b248da815625a33860e, sha256 7b6785dd9e3f43499c72e1ff0d1bdba0a9489f57c96fd85c5c0bb8682c349d0c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_support_pushforward_subset

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [DecidableEq (Place K F)] (D : Divisor K F') : (Divisor.pushforward F D).support ⊆ D.support.image (fun w => w.restrict F) := by
  classical
  intro v hv
  rw [Finsupp.mem_support_iff, pushforward_apply] at hv
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
  by_contra h
  exact hne (if_neg h)
