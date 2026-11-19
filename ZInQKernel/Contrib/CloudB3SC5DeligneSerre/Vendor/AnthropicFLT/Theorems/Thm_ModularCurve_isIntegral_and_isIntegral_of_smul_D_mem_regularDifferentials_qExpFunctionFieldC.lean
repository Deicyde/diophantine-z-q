/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC (git blob 02e0a9256dff4bc11081041466220184dedfde77, sha256 e304ba0e176a6ae7fd33b62f83cf9bed795fa71779a1f886e4fceb5c97806723).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (jbar : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hx : x • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) jbar ∈
      regularDifferentials (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)))
        (x ^ 6 * jbar ^ 4 * (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^ 3) ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)))
        (x ^ (2 * Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) *
          jbar ^ (Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) + 1) *
          (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^
            Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) := by
  revert M Γ hΓ₁ hΓ₀ jbar hjbar x hx
  exact @_root_.P2MW.S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC.solution
