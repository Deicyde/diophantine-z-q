/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div (git blob 4b4c17f65550f6c54f7a5c9eb809fbb394e178c3, sha256 15b5b5114f5e6194040e0c48240966c94952b9f386cecaa6e153fc0176babfdb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open Polynomial

theorem AlgebraicCurve.Place.ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {j : F} (hj : j ∉ v.toValuationSubring)
    {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ P.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    (hQc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ Q.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    {x : F} (hx : P.eval x = 0) (hx' : Q.eval x⁻¹ = 0) :
    v.ord x = 0 := by
  revert K F v j hj P Q hP hQ hPc hQc x hx hx'
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div.solution
