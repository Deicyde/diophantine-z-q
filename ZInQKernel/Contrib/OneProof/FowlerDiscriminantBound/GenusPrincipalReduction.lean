module

public import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.GenusKernelCard
public import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.GenusSquareRelations
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! Squarefree relations imply the genus divisibility once the prime-ideal map is given. -/

public section

namespace HDec.CMBranch.FowlerArithmetic

/-- A prime divides a squarefree subset product of primes exactly at its own index. -/
theorem prime_dvd_prime_finset_prod_iff {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) : p ∣ (∏ q ∈ s, q) ↔ p ∈ s := by
  induction s using Finset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | insert q s hq ih =>
    rw [Finset.prod_insert hq, hp.dvd_mul, ih (fun a ha => hs a (Finset.mem_insert_of_mem ha)),
      (hs q (Finset.mem_insert_self q s)).dvd_iff_eq hp.ne_one, Finset.mem_insert, eq_comm (a := q)]

/-- The product of distinct rational primes is squarefree. -/
theorem squarefree_prime_finset_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq d hdp hdq
    apply isUnit_iff_dvd_one.mpr
    by_cases h : d = 1
    · simp [h]
    · have hp' : p = d := ((hs p hp).dvd_iff_eq h).mp hdp
      have hq' : q = d := ((hs q hq).dvd_iff_eq h).mp hdq
      exact (hpq (hp'.trans hq'.symm)).elim
  · intro p hp
    exact (hs p hp).squarefree

/-- Equality of products of two finite subsets of rational primes identifies the subsets. -/
theorem prime_finset_eq_of_prod_eq {s t : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (heq : (∏ p ∈ s, p) = ∏ p ∈ t, p) : s = t := by
  exact Finset.Subset.antisymm
    (fun p hp => (prime_dvd_prime_finset_prod_iff (hs p hp) t ht).mp
      (heq ▸ (prime_dvd_prime_finset_prod_iff (hs p hp) s hs).mpr hp))
    (fun p hp => (prime_dvd_prime_finset_prod_iff (ht p hp) s hs).mp
      (heq.symm ▸ (prime_dvd_prime_finset_prod_iff (ht p hp) t ht).mpr hp))

open NumberField

/-- Isolate the exact arithmetic use of squarefree products for the class-number divisibility.
The finite index type is the set of rational prime divisors of the actual field discriminant.
The remaining inputs are the ideal classes and the principal-generator calculation. -/
theorem classNumber_genus_dvd_of_principal_squares
    {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    (hk : Module.finrank ℚ K = 2)
    (f : Multiplicative (↥(NumberField.discr K).natAbs.primeFactors → ZMod 2) →*
      ClassGroup (𝓞 K))
    (m : f.ker → ℕ) (hm : Function.Injective m) (hs : ∀ a, Squarefree (m a))
    (h : ∀ a, ∃ x : K, x ^ 2 = (m a : K) ∨ x ^ 2 = -(m a : K)) :
    2 ^ ((NumberField.discr K).natAbs.primeFactors.card - 1) ∣ classNumber K := by
  have hker := card_le_two_of_squarefree_square_relations hk m hm hs h
  have hd := pow_pred_card_dvd_of_card_ker_le_two f hker
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card] at hd
  exact hd

end HDec.CMBranch.FowlerArithmetic
