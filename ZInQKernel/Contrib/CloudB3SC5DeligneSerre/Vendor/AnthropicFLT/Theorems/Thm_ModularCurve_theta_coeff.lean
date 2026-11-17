/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_theta_coeff (git blob 59671b5ef3f2b4102fb3aa91a3c70e2701b5e02f, sha256 eddee9712c7da674a29a5cd77c436d9f1527f22dcc3d44c8d99b7bf3edbcdac0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_theta_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.theta_coeff {R : Type*} [CommRing R] (f : LaurentSeries R) (k : ℤ) : ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f).coeff k = k • f.coeff k := by
  revert R f k
  exact @_root_.P2MW.S_ModularCurve_theta_coeff.solution
