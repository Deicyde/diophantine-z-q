/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero (git blob fd9a69da229a925bb4b8842e2d4e8d8290f983ce, sha256 22e4a6b9860b11c5a5136721a861fb66e3240497f3e17da48bc14c4802b315fb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.toricPoint_add_nonToricPoint_of_charZero
    (F : Type u) [Field F] [CharZero F] [DecidableEq (LaurentSeries F)] (M : ℕ) [NeZero M] :
    (∀ (c d : Fˣ) (j : ℕ), (c : F) ≠ 1 → 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2),
        (Point.some (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2 hcd) ∧
    (∀ (c d : Fˣ) (i j : ℕ), 0 < i → 0 < j → i + j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c i).1 (nonToricPoint F M c i).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2),
        (Point.some (nonToricPoint F M c i).1 (nonToricPoint F M c i).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2
              hcd) ∧
    (∀ (c : Fˣ) (j : ℕ), 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c j).1 (nonToricPoint F M c j).2)
        (hc' : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2),
        (Point.some (nonToricPoint F M c j).1 (nonToricPoint F M c j).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2 hc'
          = 0) := by
  revert F M
  exact @_root_.P2MW.S_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.solution
