/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_exists_dvd_pow_of_krullDimLE_one (git blob 97cfd37c69ac85cb222ee489bb9ae0aacb9fad8e, sha256 170ba48c03d7b54ffacc26364cad9c04e4865b019ec3c49752796bb96a150316).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem IsLocalRing.exists_dvd_pow_of_krullDimLE_one
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  revert R b hb c hc
  exact @_root_.P2MW.S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.solution
