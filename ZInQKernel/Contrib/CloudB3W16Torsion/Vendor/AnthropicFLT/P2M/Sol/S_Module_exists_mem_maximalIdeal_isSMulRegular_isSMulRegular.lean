/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular. Apache-2.0.
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

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_Module_exists_mem_maximalIdeal_isSMulRegular_isSMulRegular

theorem solution {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (N₁ N₂ : Type*) [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] (h₁ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₁) (h₂ : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal R) N₂) :
    ∃ z ∈ IsLocalRing.maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  by_contra hcon
  have hsub : (IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂ : Set (Ideal R)), (p : Set R) := by
    intro z hz
    rw [Set.biUnion_union]
    by_cases hreg : IsSMulRegular N₁ z
    · refine Set.mem_union_right _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₂]
      exact fun hreg2 => hcon ⟨z, hz, hreg, hreg2⟩
    · refine Set.mem_union_left _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₁]
      exact hreg
  have hfin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hprime : ∀ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂),
      p ≠ (⊥ : Ideal R) → p ≠ (⊥ : Ideal R) → (id p).IsPrime := by
    rintro p (hp | hp) - -
    · exact hp.isPrime
    · exact hp.isPrime
  obtain ⟨p, hpmem, hple⟩ := (Ideal.subset_union_prime_finite hfin (f := id)
    (I := IsLocalRing.maximalIdeal R) ⊥ ⊥ hprime).mp (by simpa using hsub)
  have hpprime : p.IsPrime := by
    rcases hpmem with hp | hp
    · exact hp.isPrime
    · exact hp.isPrime
  have hpeq : p = IsLocalRing.maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpprime.ne_top) hple
  rw [hpeq] at hpmem
  rcases hpmem with hp | hp
  · exact h₁ hp
  · exact h₂ hp
