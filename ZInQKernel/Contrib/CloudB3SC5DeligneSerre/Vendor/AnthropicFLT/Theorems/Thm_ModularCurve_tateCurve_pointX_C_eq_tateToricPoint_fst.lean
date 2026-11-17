/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst (git blob 208fc37e8a734b508a45c1f74e674e9aa6bd10b6, sha256 36ad18629715b16cf04bad8fe0b88469ee3c2f9f2a11d319039521873a5ec8bc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LaurentSeries_XAdic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_KatzLevelPCusps
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped LaurentSeries.XAdic

theorem ModularCurve.tateCurve_pointX_C_eq_tateToricPoint_fst (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (hc : (c : F) ≠ 1) :
    TateCurve.pointX ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C (c : F))
      = (ModularCurve.tateToricPoint F p c).1 := by
  revert F p c hc
  exact @_root_.P2MW.S_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst.solution
