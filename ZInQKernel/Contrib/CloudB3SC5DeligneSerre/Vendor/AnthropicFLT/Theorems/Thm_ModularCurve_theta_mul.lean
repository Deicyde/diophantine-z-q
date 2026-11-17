/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_theta_mul (git blob 3a5e34c2c78cb8c9b3f90105a1307241d3a292c3, sha256 02b9a8ed140b3e378e82a63563c70e10a40ce5ef3c0930a1bf552a1a474c3c7c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_theta_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.theta_mul {R : Type*} [CommRing R] (f g : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (f * g) = f * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R g) + g * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) := by
  revert R f g
  exact @_root_.P2MW.S_ModularCurve_theta_mul.solution
