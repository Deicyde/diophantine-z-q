/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar (git blob 1875aa49eac4dad550a4288d73f1e8f3b4a9fba9, sha256 43d40026d584f7a7c197b125f746a878c29655675678fa8f4cf473cbb49d4f21).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.principal_le_closure_divisor_laurentIntegral_diamondAutHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) (d : (ZMod M)ˣ) :
    AlgebraicCurve.Divisor.principal (K := AlgebraicClosure ℚ) (F := ModularCurve.xHFunctionFieldBar M H) ≤
      AddSubgroup.closure
        {D | ∃ (y u : LaurentSeries A)
            (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.xHFunctionFieldBar M H),
            ModularCurve.coeffMap A.subtype u =
              ((ModularCurve.diamondAutHBar M H d ⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
                  ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) u ∈
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) u ≠ 0 ∧
            ∀ P, D P = P.ord (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
              ModularCurve.xHFunctionFieldBar M H)} := by
  revert M H ℓ hℓM A hA hin d
  exact @_root_.P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.solution
