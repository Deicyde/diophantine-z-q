/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk (git blob 1cbb45739d934e91c0f4663de3361ded50af6c21, sha256 549a866144f5048e1387e9444a1ff62fbc2933d556d809bddcf84894a0e9cf1b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qExpansion_E6_eq_map_mk

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane ModularForm Finset
theorem ModularCurve.qExpansion_E6_eq_map_mk :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ =
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := @_root_.P2MW.S_ModularCurve_qExpansion_E6_eq_map_mk.solution
