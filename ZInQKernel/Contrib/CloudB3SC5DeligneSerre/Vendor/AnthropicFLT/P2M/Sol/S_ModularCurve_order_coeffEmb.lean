/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_order_coeffEmb (git blob acef9910e7769f24053c9941b2b6c1cadd5b9a6d, sha256 b81fe2ccaf8a11308f95daadf28e89a14f0b295f27bcab90088b53df0f75b15d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_order_coeffEmb

open ModularCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (x : LaurentSeries ℚ) : (coeffEmb L x).order = x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, HahnSeries.order_zero, HahnSeries.order_zero]
  have hLx : coeffEmb L x ≠ 0 := by
    intro h0
    have h1 : (coeffEmb L x).coeff x.order = 0 := by rw [h0]; rfl
    rw [coeffEmb_coeff, map_eq_zero_iff _ (algebraMap ℚ L).injective] at h1
    exact HahnSeries.coeff_order_eq_zero.not.mpr hx h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_)
    (HahnSeries.order_le_of_coeff_ne_zero ?_)
  · rw [coeffEmb_coeff]
    exact fun h => HahnSeries.coeff_order_eq_zero.not.mpr hx
      ((map_eq_zero_iff _ (algebraMap ℚ L).injective).mp h)
  · intro h
    exact HahnSeries.coeff_order_eq_zero.not.mpr hLx (by rw [coeffEmb_coeff, h, map_zero])
