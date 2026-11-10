import ZInQKernel.Hypotheses.PrimeAP

/-!
Audit check: `GoodPrimeAP` follows from a Lean form of Green–Tao 2008, Theorem 1.2, and the
positive-upper-density part of Proposition D, with no further condition.

* `GreenTaoDense` is Theorem 1.2 (with "infinitely many" weakened to "one"): a set `A` of primes
  with `limsup π(N)⁻¹ |A ∩ [1, N]| > 0` contains a `k`-term progression `x + j d` (`d ≠ 0`, in `ℤ`).
  The hypothesis `limsup > 0` is written `∃ δ > 0, ∃ᶠ N, δ π(N) ≤ |A ∩ [0, N]|`, which is
  equivalent (the ratio is at most `1`, and `0 ∉ A`).
* `PropDUpper` is the part of Proposition D used: `GoodSlopePrime` has positive relative upper
  density in the primes.
-/

namespace AudAP

open Filter Classical

def GreenTaoDense : Prop :=
  ∀ A : Set ℕ, (∀ p ∈ A, p.Prime) →
    (∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N in atTop,
      δ * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)) →
    ∀ k : ℕ, ∃ x d : ℤ, d ≠ 0 ∧ ∀ j : ℕ, j < k → ∃ p ∈ A, (p : ℤ) = x + j * d

def PropDUpper : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N in atTop,
    δ * (Nat.primeCounting N : ℝ) ≤
      (((Finset.range (N + 1)).filter ZInQ.GoodSlopePrime).card : ℝ)

theorem goodPrimeAP_of_greenTao_propD (hGT : GreenTaoDense) (hD : PropDUpper) :
    ZInQ.GoodPrimeAP := by
  obtain ⟨δ, hδ, hfreq⟩ := hD
  set M : ℕ := ZInQ.Mult.S_b.sup id with hM
  have hMb : ∀ q ∈ ZInQ.Mult.S_b, q ≤ M := fun q hq => Finset.le_sup (f := id) hq
  set A : Set ℕ := {p | ZInQ.GoodSlopePrime p ∧ M < p} with hA
  have hAprime : ∀ p ∈ A, p.Prime := fun p hp => hp.1.1
  -- removing the primes `≤ M` costs at most `M + 1`
  have hcount : ∀ N : ℕ, ((((Finset.range (N + 1)).filter ZInQ.GoodSlopePrime).card : ℕ) : ℝ) ≤
      (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) + (M + 1) := by
    intro N
    have hsub : (Finset.range (N + 1)).filter ZInQ.GoodSlopePrime ⊆
        (Finset.range (N + 1)).filter (· ∈ A) ∪ Finset.range (M + 1) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, hA,
        Set.mem_ofPred_eq] at hp ⊢
      by_cases h : M < p
      · exact Or.inl ⟨hp.1, hp.2, h⟩
      · exact Or.inr (by omega)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hev : ∀ᶠ N in atTop, ((M : ℝ) + 1) ≤ δ / 2 * (Nat.primeCounting N : ℝ) := by
    have ht := Nat.tendsto_primeCounting
    have : ∀ᶠ N in atTop, ⌈2 * ((M : ℝ) + 1) / δ⌉₊ ≤ Nat.primeCounting N :=
      ht.eventually (eventually_ge_atTop _)
    filter_upwards [this] with N hN
    have h1 : 2 * ((M : ℝ) + 1) / δ ≤ Nat.primeCounting N :=
      (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hdense : ∃ δ' : ℝ, 0 < δ' ∧ ∃ᶠ N in atTop,
      δ' * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) := by
    refine ⟨δ / 2, by positivity, ?_⟩
    refine (hfreq.and_eventually hev).mono fun N ⟨h1, h2⟩ => ?_
    have := hcount N
    linarith
  intro K
  obtain ⟨x, d, hd, hprog⟩ := hGT A hAprime (by convert hdense) (K + 1)
  -- the terms of the progression, as natural numbers in `A`
  choose! p hpA hpeq using fun j (hj : j < K + 1) => hprog j hj
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · -- reverse the progression
    refine ⟨p K, (-d).toNat, (hpA K (by omega)).1.1.one_lt.le, by omega, fun j hj => ?_⟩
    have hj' : K - j < K + 1 := by omega
    have e : p K + j * (-d).toNat = p (K - j) := by
      have h1 := hpeq K (by omega)
      have h2 := hpeq (K - j) hj'
      have : ((p K + j * (-d).toNat : ℕ) : ℤ) = (p (K - j) : ℤ) := by
        push_cast
        rw [Int.toNat_of_nonneg (by omega), h1, h2, Nat.cast_sub (by omega)]
        ring
      exact_mod_cast this
    rw [e]
    obtain ⟨hg, hMp⟩ := hpA (K - j) hj'
    exact ⟨hg, fun q hq => (hMb q hq).trans_lt hMp⟩
  · refine ⟨p 0, d.toNat, (hpA 0 (by omega)).1.1.one_lt.le, by omega, fun j hj => ?_⟩
    have hj' : j < K + 1 := by omega
    have e : p 0 + j * d.toNat = p j := by
      have h1 := hpeq 0 (by omega)
      have h2 := hpeq j hj'
      have : ((p 0 + j * d.toNat : ℕ) : ℤ) = (p j : ℤ) := by
        push_cast
        rw [Int.toNat_of_nonneg (by omega), h1, h2]
        ring
      exact_mod_cast this
    rw [e]
    obtain ⟨hg, hMp⟩ := hpA j hj'
    exact ⟨hg, fun q hq => (hMb q hq).trans_lt hMp⟩

end AudAP

#print axioms AudAP.goodPrimeAP_of_greenTao_propD
