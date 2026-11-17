/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex (git blob fef2b2b133aecb08061d8204ef4242dcdf9f6d7d, sha256 dc2237cab9f7f3b77f112d24ca7f382d4b363ecc62cad069147d33dfd1a7998c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex
    (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hind : Γ'.relIndex Γ ≠ 0) :
    IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}) ≤
      (Γ'.relIndex Γ : Cardinal) := by
  revert Γ Γ' hle hT hind
  exact @_root_.P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.solution
