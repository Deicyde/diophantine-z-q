/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v

theorem Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
    {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C] :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C), AlgebraicIndependent R z ∧
      ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType.solution
