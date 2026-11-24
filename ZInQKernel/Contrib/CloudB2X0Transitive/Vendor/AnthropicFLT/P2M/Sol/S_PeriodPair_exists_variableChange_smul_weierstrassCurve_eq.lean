/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_surjective
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq

set_option autoImplicit false

theorem solution (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • L.weierstrassCurve = E := by
  obtain ⟨L, hΔ, hj⟩ := PeriodPair.jLattice_surjective E.j
  haveI : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ.weierstrassCurve_Δ_ne_zero⟩
  have hjE : L.weierstrassCurve.j = E.j := by
    rw [← hj, L.jLattice_eq_c₄_pow_three_div_Δ, WeierstrassCurve.j, div_eq_mul_inv, mul_comm,
      Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  exact ⟨L, WeierstrassCurve.exists_variableChange_of_j_eq L.weierstrassCurve E hjE⟩
