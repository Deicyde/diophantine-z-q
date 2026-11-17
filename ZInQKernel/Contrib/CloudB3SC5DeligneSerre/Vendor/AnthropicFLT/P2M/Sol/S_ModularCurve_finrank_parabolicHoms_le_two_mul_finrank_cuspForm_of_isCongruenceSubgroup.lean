/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup (git blob 609d2fb2df05f1af2ed15e7ed775735123978022, sha256 65f2d05fb4763d4e5899af278eaaf4f90d1521a1441d40b8295669b8ca10ccab).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
export _root_.ModularCurve (Period.parabolicHoms finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm)
namespace ESSurjCongruence
open _root_.ModularCurve

theorem main (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) := by
  obtain ⟨N, hN, hle⟩ := hΓ
  haveI : NeZero N := ⟨hN⟩
  haveI : (CongruenceSubgroup.Gamma N).Normal := CongruenceSubgroup.Gamma_normal N
  haveI : ((CongruenceSubgroup.Gamma N).subgroupOf Γ).Normal := inferInstance
  exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
    (CongruenceSubgroup.Gamma N) Γ hle inferInstance
    (ModularCurve.finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm N)

end ModularCurve.ESSurjCongruence

theorem solution (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ) ≤
      2 * Module.finrank ℂ (CuspForm Γ 2) :=
  ModularCurve.ESSurjCongruence.main Γ hΓ
