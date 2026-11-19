/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (git blob 5b022e8d6ca96702dd79801765ccd256d1ad2cab, sha256 455c5d0d46a953b1d68dd082ae6063f8b1a9407b49f0591b550acca180433f65).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodHomPair
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) (k : ℤ)
    (f : CuspForm Γ k) :
    ∃ g : CuspForm Γ k, ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)) := by
  revert Γ hΓ k f
  exact @_root_.P2MW.S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem.solution
