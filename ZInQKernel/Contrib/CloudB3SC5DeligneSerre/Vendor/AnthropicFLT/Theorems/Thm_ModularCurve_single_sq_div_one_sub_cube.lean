/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_single_sq_div_one_sub_cube (git blob 33d2ddcb49fa2a0cc3d157d32087215082c61ae5, sha256 16f8349103a6902378a0d851e1eb3830b74e3594b21b3f5987cf65ffabcf91b2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.LaurentSeries
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_single_sq_div_one_sub_cube

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.single_sq_div_one_sub_cube (K : Type*) [Field K] (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c ^ 2 / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 3 =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0) := by
  revert K j hj c
  exact @_root_.P2MW.S_ModularCurve_single_sq_div_one_sub_cube.solution
