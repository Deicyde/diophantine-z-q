/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast (git blob 3b2fef6cf8f7c69502546b2aeed6166a99dc350e, sha256 fd938acce629a503add8d91a50c44ba4b5a26fcb59e1cc4cfa5bccf1d7bcdee0).
Modified for the Z-in-Q kernel (2026-11-16, cluster C5): import paths relocated (modules already
vendored elsewhere in the kernel are imported from there), the upstream lakefile options set as
`set_option` lines, and: dropped import P2M.Util (wrapper commands replaced by ordinary Lean); replaced 1 proof-wrapper tactic call(s) by `revert` + `exact` of the paired Sol proof.
Any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Module.Basis.exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J) (i i' : ι), b.repr (S j (b i)) i' ∈ Set.range ((↑) : ℚ → ℂ))
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ i : ι, ℓ (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (lam : J → ℂ) (v : V) (hv : ∀ j : J, S j v = lam j • v) (hℓv : ℓ v ≠ 0)
    (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] (hR : ∀ j : J, lam j ∈ R) (τ : R →+* ℂ) :
    ∃ w : V, ℓ w ≠ 0 ∧ ∀ j : J, S j w = τ ⟨lam j, hR j⟩ • w := by
  revert ι V b J S hS ℓ hℓ lam v hv hℓv R hR τ
  exact @_root_.P2MW.S_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast.solution
