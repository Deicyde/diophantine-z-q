/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex (git blob 83627f01388dd5cc671401cbdd1d9bd8ba475f49, sha256 a9bd59f977d590d936005ecf4d218168dacc5f376dc7a444fc2be65850025c37).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (ℓ : Module.Dual ℂ (CuspForm Γ 2)) :
    ∃ f : CuspForm Γ 2,
      ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 f g τ) = ℓ g := by
  revert Γ ℓ
  exact @_root_.P2MW.S_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex.solution
