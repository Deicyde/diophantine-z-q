/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RadialRegion_exists_refine_exact (git blob 3aaeff6a71bc9533f0cc6c6dad0422d13f55773a, sha256 ddcb3adfd99dd2bb2486f0ed0cb04f9a26f2856d7df27f8536501b69b919c1b1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RadialRegion_exists_refine_exact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_refine_exact (R : RadialRegion) (T : Finset ℝ)
    (hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 2 * π) :
    ∃ R' : RadialRegion,
      R'.q = R.q ∧ R'.r = R.r ∧ R'.K = R.K ∧ R'.Kint = R.Kint ∧ R'.loop = R.loop ∧
      Set.range R'.φs = Set.range R.φs ∪ (T : Set ℝ) ∧
      R'.N + 1 = (Set.range R.φs ∪ (T : Set ℝ)).ncard ∧
      (∀ k' : Fin R'.N, ∀ t ∈ Set.range R.φs ∪ (T : Set ℝ),
        t ∉ Ioo (R'.φs k'.castSucc) (R'.φs k'.succ)) ∧
      (∀ k' : Fin R'.N, ∃ k : Fin R.N, R'.arcIcc k' ⊆ R.arcIcc k) := by
  revert R T hT
  exact @_root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_refine_exact.solution
