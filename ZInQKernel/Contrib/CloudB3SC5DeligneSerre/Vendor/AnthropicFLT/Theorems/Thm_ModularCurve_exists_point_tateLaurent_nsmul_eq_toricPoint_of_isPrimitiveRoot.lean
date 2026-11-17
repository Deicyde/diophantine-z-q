/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot (git blob c742afe98330c119cbcec1bf8dcf6053f87fb7c9, sha256 e47da1f5caa731284fe160cab22a301fd50913a418688b55de5712c9aca64002).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u v in

theorem ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M)
    (L : Type v) [Field L] [DecidableEq L] [Algebra (LaurentSeries K) L] :
    ∃ P : ((tateLaurent K).baseChange L).toAffine.Point,
      (∀ n : ℕ, n • P = 0 ↔ M ∣ n) ∧
      ∀ n : ℕ, ¬ M ∣ n →
        ∃ h : ((tateLaurent K).baseChange L).toAffine.Nonsingular
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2),
          n • P = WeierstrassCurve.Affine.Point.some
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2) h := by
  revert K M hM ζ hζ L
  exact @_root_.P2MW.S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.solution
