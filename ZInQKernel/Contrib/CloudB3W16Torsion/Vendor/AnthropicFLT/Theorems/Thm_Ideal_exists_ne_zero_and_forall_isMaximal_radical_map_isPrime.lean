/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v w

theorem Ideal.exists_ne_zero_and_forall_isMaximal_radical_map_isPrime
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C] [FaithfulSMul R C]
    (hgi : ∀ θ : FractionRing C,
      IsSeparable (IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) θ →
      θ ∈ IntermediateField.adjoin k (Set.range (algebraMap R (FractionRing C)))) :
    ∃ r : R, r ≠ 0 ∧ ∀ n : Ideal R, n.IsMaximal → r ∉ n →
      n.map (algebraMap R C) = ⊤ ∨ (n.map (algebraMap R C)).radical.IsPrime := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_ne_zero_and_forall_isMaximal_radical_map_isPrime.solution
