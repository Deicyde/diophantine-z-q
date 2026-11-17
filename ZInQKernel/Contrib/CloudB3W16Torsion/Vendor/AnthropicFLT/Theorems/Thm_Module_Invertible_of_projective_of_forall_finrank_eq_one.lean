/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_Invertible_of_projective_of_forall_finrank_eq_one

set_option backward.isDefEq.respectTransparency false

universe u v

theorem Module.Invertible.of_projective_of_forall_finrank_eq_one
    {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_projective_of_forall_finrank_eq_one.solution
