/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd (git blob 24f3596c7e18a6a0fa42df87ba0270aead3614e7, sha256 61a72ef544a01c4c0377175ddffc6a871fb9b4866d3c08858b0ed798a7f0c4f6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LaurentSeries_XAdic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_KatzLevelPCusps
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped LaurentSeries.XAdic

theorem ModularCurve.tateCurve_pointY_C_eq_tateToricPoint_snd (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (hc : (c : F) ≠ 1) :
    TateCurve.pointY ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C (c : F))
      = (ModularCurve.tateToricPoint F p c).2 := by
  revert F p c hc
  exact @_root_.P2MW.S_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd.solution
