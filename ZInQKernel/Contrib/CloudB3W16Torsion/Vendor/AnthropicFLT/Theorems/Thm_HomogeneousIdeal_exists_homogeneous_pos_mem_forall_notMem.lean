/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem

set_option backward.isDefEq.respectTransparency false

universe u v

theorem HomogeneousIdeal.exists_homogeneous_pos_mem_forall_notMem
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (I : HomogeneousIdeal 𝒜) (hirr : I ≤ HomogeneousIdeal.irrelevant 𝒜)
    (t : Finset (HomogeneousIdeal 𝒜)) (hprime : ∀ p ∈ t, p.toIdeal.IsPrime) (havoid : ∀ p ∈ t, ¬ I ≤ p) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ p ∈ t, x ∉ p := by p2m_exact_reverting @_root_.P2MW.S_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem.solution
