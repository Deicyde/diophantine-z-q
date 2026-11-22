/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜) [IsAffineHom ι] (S : Finset X) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj.solution
