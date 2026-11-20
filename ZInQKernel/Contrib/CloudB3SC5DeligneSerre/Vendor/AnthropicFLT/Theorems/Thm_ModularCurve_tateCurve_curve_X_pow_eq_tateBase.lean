/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase (git blob 2b944bcbf55f60ae897b399a778895a816b06185, sha256 650723f9eddd74d0ae35dd29d9c0ba1798be8fb9aa8ab02c5c8ae800aa0a172e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LaurentSeries_XAdic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_PointSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_tateCurve_curve_X_pow_eq_tateBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped LaurentSeries.XAdic

theorem ModularCurve.tateCurve_curve_X_pow_eq_tateBase (F : Type*) [Field F] (p : ℕ) [NeZero p] :
    TateCurve.curve ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) = ModularCurve.tateBase F p := by
  revert F p
  exact @_root_.P2MW.S_ModularCurve_tateCurve_curve_X_pow_eq_tateBase.solution
