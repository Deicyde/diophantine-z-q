/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int (git blob 90fbff3beb9949349013450bb4123b0c8da6fa01, sha256 39bc83d0f51a52df38da5e279a6e4c649aeef751186b52bad5f3045857dd7a94).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (f : CuspForm Γ 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 f g τ) = Λ g) ↔
      ∀ γ : Γ, ∃ m : ℤ, (ModularCurve.periodOf Γ γ f).re = m := by
  revert Γ hΓ hneg f
  exact @_root_.P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int.solution
