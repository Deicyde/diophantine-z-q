/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Prime
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular

set_option backward.isDefEq.respectTransparency false

theorem Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (N₁ N₂ : Type*) [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] (h₁ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₁) (h₂ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₂) :
    ∃ z ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular.solution
