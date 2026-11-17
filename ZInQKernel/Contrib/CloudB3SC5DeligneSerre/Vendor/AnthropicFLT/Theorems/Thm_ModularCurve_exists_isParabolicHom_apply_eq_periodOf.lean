/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_periodOf (git blob 3c9d84b1a7ed8479a8d09e880aa11c559c384c1e, sha256 7202f2949b040ab5255e37b18cc24db2a016371b70138c2bca650a5989b654b8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isParabolicHom_apply_eq_periodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_isParabolicHom_apply_eq_periodOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ Φ : Additive Γ →+ Module.Dual ℂ (CuspForm Γ 2),
      ModularCurve.Period.IsParabolicHom Γ Φ ∧
        ∀ γ : Γ, Φ (Additive.ofMul γ) = ModularCurve.periodOf Γ γ := by
  revert Γ
  exact @_root_.P2MW.S_ModularCurve_exists_isParabolicHom_apply_eq_periodOf.solution
