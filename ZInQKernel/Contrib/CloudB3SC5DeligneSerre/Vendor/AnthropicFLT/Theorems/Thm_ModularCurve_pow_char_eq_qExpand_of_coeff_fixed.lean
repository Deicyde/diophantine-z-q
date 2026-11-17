/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed (git blob cd231d4dc19cb68a42c1d7602a96b81dd9b3e0e4, sha256 7d4ae6d167d84a5d938c6df4591159ad76984bb99688e76845b812aca18ef2ef).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.pow_char_eq_qExpand_of_coeff_fixed {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (s : LaurentSeries R) (hfix : ∀ k : ℤ, (s.coeff k) ^ p = s.coeff k) :
    s ^ p = qExpand R p s := by
  revert R p s hfix
  exact @_root_.P2MW.S_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed.solution
