/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul (git blob ad291818c57f3dce2f9fa28b7e95f54f30fc1799, sha256 f2d0b6539785a4ee2d9a05057e5eea7188e9fe680ae3d76cd46f4a5ab638af5d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.relfinrank_x1HeckeCompositum_eq_mul (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))) := by
  revert L M ℓ ℓ' hℓ
  exact @_root_.P2MW.S_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.solution
