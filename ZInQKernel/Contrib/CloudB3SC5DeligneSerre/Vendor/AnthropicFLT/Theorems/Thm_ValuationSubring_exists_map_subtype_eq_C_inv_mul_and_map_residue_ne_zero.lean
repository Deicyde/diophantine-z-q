/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero (git blob a2ce4b94a2ecbaccd1815112ffc9450e3956350f, sha256 803b780ccc5a93e0f1070c514b30e7bc9ef783a201ec6f8b240a118486317ec1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    (q₁ : Polynomial L) (hq₁ : q₁ ≠ 0) :
    ∃ q : Polynomial A, ∃ c : L, c ≠ 0 ∧
      (q.map A.subtype = Polynomial.C c⁻¹ * q₁) ∧ q.map (IsLocalRing.residue A) ≠ 0 := by
  revert L A q₁ hq₁
  exact @_root_.P2MW.S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.solution
