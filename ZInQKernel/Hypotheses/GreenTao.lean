import ZInQKernel.Hypotheses.PrimeAP

/-!
# Hypothesis 22P_AP from Green–Tao (dense form) and Proposition D

The trust statement of `GoodPrimeAP` (hypothesis 22P_AP) splits into two named statements:

* `GreenTaoDense`: Szemerédi's theorem in the primes (Green–Tao 2008, Theorem 1.2; complete proof
  in Tao–Ziegler 2008): a set of primes of positive relative upper density contains arithmetic
  progressions of every finite length;
* `GoodPrimeDensity`: the good slope primes (`GoodSlopePrime`) have positive relative upper density
  in the primes (Proposition D of `docs/research/nt-22p.md`).

`goodPrimeAP_of_greenTaoDense` derives `GoodPrimeAP` from the two, with no further input.
-/

namespace ZInQ

open Filter

/-- A set `A ⊆ ℕ` contains arithmetic progressions of every finite length: for every `k` there are
`a` and `b ≥ 1` with `a + b j ∈ A` for all `j < k`. This is the shape of the conclusion of
`green_tao` in the lean-eval benchmark, so that an imported proof fits. -/
def ContainsArbitraryAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A

open Classical in
/-- `A` has positive relative upper density in the primes: there is `c > 0` such that, for
infinitely many `N`, `c · π(N) ≤ |A ∩ [0, N]|`. For a set of primes this is
`limsup_{N → ∞} |A ∩ [1, N]| / π(N) > 0`. -/
def PrimesRelUpperDensityPos (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ N in atTop,
    c * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)

/-- **Green–Tao, dense form.** Every set of primes of positive relative upper density contains
arithmetic progressions of every finite length.

**Trust statement.** Not proved in Lean. This is Theorem 1.2 of B. Green and T. Tao, *The primes
contain arbitrarily long arithmetic progressions*, Ann. of Math. 167 (2008), 481–547 (Szemerédi's
theorem in the primes; here with "infinitely many progressions" weakened to "one"). Green and Tao
prove Theorem 1.2 there only in outline (section 11 of arXiv math/0404188v6). A complete proof of
the needed form is the main theorem of T. Tao and T. Ziegler, *The primes contain arbitrarily long
polynomial progressions*, Acta Math. 201 (2008), 213–305, applied with the linear polynomials
`P_i = (i − 1) m`. The published Lean proofs of Green–Tao known to the project prove the statement
only for the set of all primes (Theorem 1.1, the lean-eval `green_tao` statement), not this dense
form. -/
def GreenTaoDense : Prop :=
  ∀ A : Set ℕ, A ⊆ {p | p.Prime} → PrimesRelUpperDensityPos A → ContainsArbitraryAPs A

/-- **Proposition D (upper density part).** The good slope primes (`GoodSlopePrime`) have positive
relative upper density in the primes.

**Trust statement.** Not proved in Lean. This is Proposition D of `docs/research/nt-22p.md`: the
good slope primes have relative density about `0.106` in the primes, from the CM description of
the reductions of the curves involved, the prime number theorem in progressions and an elementary
lattice sieve. Its proof is written on paper only as a sketch. -/
def GoodPrimeDensity : Prop :=
  PrimesRelUpperDensityPos {p | GoodSlopePrime p}

/-- **22P_AP from Green–Tao and Proposition D.** Removing the finitely many primes `≤ max S_b`
keeps positive relative upper density (since `π(N) → ∞`); Green–Tao then gives the progressions. -/
theorem goodPrimeAP_of_greenTaoDense (hGT : GreenTaoDense) (hD : GoodPrimeDensity) :
    GoodPrimeAP := by
  classical
  obtain ⟨δ, hδ, hfreq⟩ := hD
  set M : ℕ := Mult.S_b.sup id with hM
  have hMb : ∀ q ∈ Mult.S_b, q ≤ M := fun q hq => Finset.le_sup (f := id) hq
  set A : Set ℕ := {p | GoodSlopePrime p ∧ M < p} with hA
  have hAprime : A ⊆ {p | p.Prime} := fun p hp => hp.1.1
  -- removing the primes `≤ M` costs at most `M + 1`
  have hcount : ∀ N : ℕ,
      ((((Finset.range (N + 1)).filter (· ∈ {p | GoodSlopePrime p})).card : ℕ) : ℝ) ≤
        (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) + (M + 1) := by
    intro N
    have hsub : (Finset.range (N + 1)).filter (· ∈ {p | GoodSlopePrime p}) ⊆
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
  have hdense : PrimesRelUpperDensityPos A := by
    refine ⟨δ / 2, by positivity, ?_⟩
    refine (hfreq.and_eventually hev).mono fun N ⟨h1, h2⟩ => ?_
    have h3 := hcount N
    convert (show δ / 2 * (Nat.primeCounting N : ℝ) ≤
      (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ) by linarith)
  intro K
  obtain ⟨a, b, hb, hprog⟩ := hGT A hAprime hdense (K + 1)
  refine ⟨a, b, (hAprime (hprog 0 (by omega))).one_lt.le.trans (by simp), hb, fun j hj => ?_⟩
  obtain ⟨hg, hMp⟩ := hprog j (by omega)
  rw [mul_comm j b]
  exact ⟨hg, fun q hq => (hMb q hq).trans_lt hMp⟩

end ZInQ
