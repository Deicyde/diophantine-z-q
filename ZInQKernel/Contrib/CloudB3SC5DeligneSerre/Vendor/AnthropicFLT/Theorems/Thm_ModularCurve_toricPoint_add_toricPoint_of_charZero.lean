/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_of_charZero (git blob 9c87d0dad40cbb20b827210263c72cedfa9eefca, sha256 0221599fd2459f8162fb4ac922fea0c49da01d62c216cbdf1bbb7c8839fe65e2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_toricPoint_add_toricPoint_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.toricPoint_add_toricPoint_of_charZero
    (F : Type u) [Field F] [CharZero F] [DecidableEq (LaurentSeries F)]
    (c d : F) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hc1 : c ≠ 1) (hd1 : d ≠ 1) :
    ∃ (hc : (tateLaurent F).toAffine.Nonsingular (toricPoint F 1 c).1 (toricPoint F 1 c).2)
      (hd : (tateLaurent F).toAffine.Nonsingular (toricPoint F 1 d).1 (toricPoint F 1 d).2),
      (c * d = 1 →
        (Point.some (toricPoint F 1 c).1 (toricPoint F 1 c).2 hc : (tateLaurent F).toAffine.Point)
          + Point.some (toricPoint F 1 d).1 (toricPoint F 1 d).2 hd = 0) ∧
      (c * d ≠ 1 →
        ∃ hcd : (tateLaurent F).toAffine.Nonsingular
            (toricPoint F 1 (c * d)).1 (toricPoint F 1 (c * d)).2,
          (Point.some (toricPoint F 1 c).1 (toricPoint F 1 c).2 hc : (tateLaurent F).toAffine.Point)
            + Point.some (toricPoint F 1 d).1 (toricPoint F 1 d).2 hd
            = Point.some (toricPoint F 1 (c * d)).1 (toricPoint F 1 (c * d)).2 hcd) := by
  revert F c d hc0 hd0 hc1 hd1
  exact @_root_.P2MW.S_ModularCurve_toricPoint_add_toricPoint_of_charZero.solution
