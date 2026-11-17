/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul (git blob 3e1a95d9491375614c2f5e05ea78cafbcd17d262, sha256 cf93347799e694d0a1769be2e5393a3e229245bf8496da12dda04a446604d3f4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem ModularCurve.relfinrank_xHHeckeCompositum_eq_mul (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by
  revert L M H ℓ ℓ' hℓ
  exact @_root_.P2MW.S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.solution
