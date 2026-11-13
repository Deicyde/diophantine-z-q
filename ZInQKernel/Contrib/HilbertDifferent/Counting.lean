/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.
Authors: The Tau Ceti contributors

Adapted from TauCetiProject/TauCeti at a6027b1d24fcb935c53bd5b50d11b40991cda418,
 RingTheory/LocalRing/RamificationGroup.lean, lines 469–514.
The counting argument is generalized from a local DVR's maximal ideal/addVal to
any nonzero prime of a Dedekind domain, using the pinned Mathlib multiplicity.
It uses no completion, local-field package, or Hilbert-formula assumption.
See docs/research/t20-hilbert-different.md for the source license and scope.
-/
import ZInQKernel.Contrib.HilbertDifferent.Generators
import ZInQKernel.Contrib.HilbertDifferent.Filtration
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Multiplicity
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace ZInQ.Contrib.HilbertDifferent

open Finset

section Counting

variable {G B R : Type*} [Group G] [CommRing B] [IsDedekindDomain B]
  [MulSemiringAction G B] [FaithfulSMul G B] [CommSemiring R]
  [Algebra R B] [SMulCommClass G R B] [Fintype G] [DecidableEq G]

/-- Hilbert's double-counting identity for the actual inertia groups of prime powers in a
monogenic Dedekind algebra. There is no local-ring or complete-field assumption. -/
theorem sum_displacementMultiplicity_eq_sum_powerInertiaCard (P : Ideal B) [P.IsPrime]
    (hP : P ≠ ⊥) {x : B} (hx : Algebra.adjoin R {x} = ⊤) {N : ℕ}
    (hN : (P ^ (N + 1)).inertia G = ⊥) :
    (∑ σ ∈ (univ : Finset G).erase 1, multiplicity P (Ideal.span {σ • x - x})) =
      ∑ i ∈ range N, (Nat.card ((P ^ (i + 1)).inertia G) - 1) := by
  classical
  let f : ℕ → Subgroup G := fun i ↦ (P ^ (i + 1)).inertia G
  have hprime : Prime P := (Ideal.prime_iff_isPrime hP).mpr inferInstance
  have hfinite (σ : G) (hσ : σ ≠ 1) :
      FiniteMultiplicity P (Ideal.span {σ • x - x}) := by
    apply FiniteMultiplicity.of_prime_left hprime
    intro hzero
    have hfix : σ • x = x := sub_eq_zero.mp (Ideal.span_singleton_eq_bot.mp hzero)
    exact hσ (eq_one_of_smul_generator_eq hx hfix)
  have htest (σ : G) (hσ : σ ≠ 1) (i : ℕ) :
      σ ∈ f i ↔ i + 1 ≤ multiplicity P (Ideal.span {σ • x - x}) := by
    change σ ∈ (P ^ (i + 1)).inertia G ↔ _
    rw [mem_inertia_iff_of_adjoin_singleton_eq_top hx, ← Ideal.dvd_span_singleton,
      (hfinite σ hσ).pow_dvd_iff_le_multiplicity]
  have hcount : ∀ σ ∈ (univ : Finset G).erase 1,
      multiplicity P (Ideal.span {σ • x - x}) =
        ((range N).filter fun i : ℕ ↦ σ ∈ f i).card := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := ne_of_mem_erase hσ
    let n := multiplicity P (Ideal.span {σ • x - x})
    have hnN : n ≤ N := by
      by_contra h
      have hmem : σ ∈ f N := (htest σ hσ1 N).mpr (by omega)
      change σ ∈ (P ^ (N + 1)).inertia G at hmem
      rw [hN, Subgroup.mem_bot] at hmem
      exact hσ1 hmem
    have hfilter : ((range N).filter fun i : ℕ ↦ σ ∈ f i) = range n := by
      ext i
      simp only [mem_filter, mem_range, htest σ hσ1]
      change (i < N ∧ i + 1 ≤ n) ↔ i < n
      omega
    rw [hfilter, card_range]
  rw [sum_congr rfl hcount]
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (σ : G) (i : ℕ) ↦ σ ∈ f i) (s := univ.erase 1) (t := range N)
  simp only [bipartiteAbove, bipartiteBelow] at hdc
  rw [hdc]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨mem_univ _, one_mem _⟩),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

end Counting

section IdealProducts

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- Multiplicity distributes over a finite product of nonzero ideals. All finiteness
hypotheses come from the nonzero prime and the explicitly nonzero product. -/
theorem multiplicity_prod_of_ne_bot {α : Type*} (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥)
    (s : Finset α) (f : α → Ideal B) (hf : ∀ a ∈ s, f a ≠ ⊥) :
    multiplicity P (∏ a ∈ s, f a) = ∑ a ∈ s, multiplicity P (f a) := by
  classical
  have hprime : Prime P := (Ideal.prime_iff_isPrime hP).mpr inferInstance
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : f a ≠ ⊥ := hf a (mem_insert_self a s)
      have hfs : ∀ b ∈ s, f b ≠ ⊥ := fun b hb ↦ hf b (mem_insert_of_mem hb)
      rw [prod_insert ha, sum_insert ha, multiplicity_mul hprime, ih hfs]
      exact FiniteMultiplicity.of_prime_left hprime
        (mul_ne_zero hfa (Finset.prod_ne_zero_iff.mpr hfs))

omit [IsDedekindDomain B] in
/-- Principal ideals carry products of ring elements to products of ideals, including the
empty product. -/
theorem span_singleton_finsetProd {α : Type*} (s : Finset α) (f : α → B) :
    Ideal.span {∏ a ∈ s, f a} = ∏ a ∈ s, Ideal.span {f a} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [prod_insert ha, prod_insert ha, ← Ideal.span_singleton_mul_span_singleton, ih]

end IdealProducts

end ZInQ.Contrib.HilbertDifferent
