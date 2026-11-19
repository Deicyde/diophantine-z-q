/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq (git blob 6c715bff9f03620afbcc8c7796cfe1a42cf63ecb, sha256 fedaa11208300fc02554a28a37569500061eb9eb9446b0fee695a6e1dc045f02).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped InnerProductSpace

theorem ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (E : Submodule ℂ H)
    (hsym : ∀ x ∈ E, ∀ y ∈ E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (v : H) (hsurj : ∀ c : ℝ, ∃ w ∈ E, T w - (c : ℂ) • w = v) :
    v = 0 := by
  revert H T E hsym v hsurj
  exact @_root_.P2MW.S_ContinuousLinearMap_eq_zero_of_forall_exists_mem_sub_real_smul_eq.solution
