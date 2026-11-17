/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_Basis_repr_mem_range_ratCast_of_forall_dual (git blob 89c1a5a0763c2ab3ba490c5054138ab0c02df1c9, sha256 6af8a6086754c99c372cb9132ec52675c1d0d8a66d1955aafc85c52ee7b9775f).
Modified for the Z-in-Q kernel (2026-11-16, cluster C5): import paths relocated (modules already
vendored elsewhere in the kernel are imported from there), the upstream lakefile options set as
`set_option` lines, and: dropped import P2M.Util (wrapper commands replaced by ordinary Lean); replaced 1 proof-wrapper tactic call(s) by `revert` + `exact` of the paired Sol proof.
Any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Module_Basis_repr_mem_range_ratCast_of_forall_dual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Module.Basis.repr_mem_range_ratCast_of_forall_dual
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {A : Type*} (φ : A → V →ₗ[ℂ] ℂ)
    (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0)
    (hφb : ∀ (a : A) (i : ι), φ a (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (h : V) (hh : ∀ a : A, φ a h ∈ Set.range ((↑) : ℚ → ℂ)) (i : ι) :
    b.repr h i ∈ Set.range ((↑) : ℚ → ℂ) := by
  revert ι V b A φ hinj hφb h hh i
  exact @_root_.P2MW.S_Module_Basis_repr_mem_range_ratCast_of_forall_dual.solution
