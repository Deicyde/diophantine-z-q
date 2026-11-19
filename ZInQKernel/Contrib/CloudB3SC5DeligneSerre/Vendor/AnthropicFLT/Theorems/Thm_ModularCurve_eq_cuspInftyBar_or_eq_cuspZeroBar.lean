/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar (git blob 035fd111ce94601bbba2caa71a15c67214b8d5a8, sha256 247d09a18b67c1404c2e2c4607b6eb660dd1e44867c05e12120f9b3d8435c5c2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CuspidalClass
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve AlgebraicCurve

theorem ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar (ℓ : ℕ) [Fact ℓ.Prime] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ)) (hc : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full ℓ)⟩ : modularFunctionFieldBar ℓ) w) : w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ := by
  revert ℓ w hc
  exact @_root_.P2MW.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.solution
