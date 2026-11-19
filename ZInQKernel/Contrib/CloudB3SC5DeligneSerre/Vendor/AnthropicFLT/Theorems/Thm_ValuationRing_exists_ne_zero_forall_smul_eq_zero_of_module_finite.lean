/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite (git blob 0920e7f0943d65b121c87b7b41f84dc626dbd9fd, sha256 0677d3a7151183dadbaed6a4bf8ffe100108065d0cb4fc75281c272e98481c2a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationRing.exists_ne_zero_forall_smul_eq_zero_of_module_finite
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : M, (∃ c : R, c ≠ 0 ∧ c • m = 0) → a • m = 0 := by
  revert R M
  exact @_root_.P2MW.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite.solution
