/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot (git blob 89041204f16b599500d8e5ed31a80d6ded2fffba, sha256 02b50c2f997c8a4024debc55e6b0124613969dcf4c269be1e09304eb4a3391d0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
    (K : Type u) [Field K] [DecidableEq (LaurentSeries K)] (M : ℕ) [NeZero M] (hM : 2 ≤ M)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) :
    ∃ (xA yA xB yB : LaurentSeries K)
      (hA : (tateBase K M).toAffine.Nonsingular xA yA)
      (hB : (tateBase K M).toAffine.Nonsingular xB yB)
      (hB' : (tateBase K M).toAffine.Nonsingular (qTwist ζ xB) (qTwist ζ yB)),
      M • (Point.some xA yA hA) = 0 ∧ M • (Point.some xB yB hB) = 0 ∧
      (∀ a b : ℤ, a • Point.some xA yA hA + b • Point.some xB yB hB = 0 →
        (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      qTwist ζ xA = xA ∧ qTwist ζ yA = yA ∧
      Point.some (qTwist ζ xB) (qTwist ζ yB) hB' = Point.some xA yA hA + Point.some xB yB hB := by
  revert K M hM ζ hζ
  exact @_root_.P2MW.S_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.solution
