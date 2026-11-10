import Mathlib

/-!
# The hypothesis that would replace `ZInQ.GoodPrimeAP`

Scratch file for `docs/research/gt-search.md` (not part of `ZInQKernel`). It depends on Mathlib
only. It states Green–Tao 2008, Theorem 1.2 (`GreenTaoDense`) in the shape of the lean-eval
statement `ContainsArbitraryAPs`, the density hypothesis `PrimesRelUpperDensityPos`, and proves
that the two give the conclusion of `ZInQ.GoodPrimeAP` for any set of primes `G` and any finite
bound set `S` (`progressions_above_of_greenTaoDense`). With `G := {p | ZInQ.GoodSlopePrime p}` and
`S := Mult.S_b` this is exactly `ZInQ.GoodPrimeAP`.
-/

open Filter

namespace GTSearch

/-- The lean-eval form (`LeanEval.NumberTheory.ContainsArbitraryAPs`). -/
def ContainsArbitraryAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A

open Classical in
/-- `A` has positive relative upper density in the primes:
`limsup_N |A ∩ [0, N]| / π(N) > 0`. -/
def PrimesRelUpperDensityPos (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ N in atTop,
    c * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)

/-- Green–Tao 2008, Theorem 1.2: a set of primes of positive relative upper density contains
arithmetic progressions of every length. -/
def GreenTaoDense : Prop :=
  ∀ A : Set ℕ, A ⊆ {p | p.Prime} → PrimesRelUpperDensityPos A → ContainsArbitraryAPs A

open Classical in
/-- Removing the numbers `≤ B` keeps positive relative upper density. -/
theorem PrimesRelUpperDensityPos.diff_le {A : Set ℕ} (hA : PrimesRelUpperDensityPos A) (B : ℕ) :
    PrimesRelUpperDensityPos (A ∩ {p | B < p}) := by
  obtain ⟨c, hc, hfreq⟩ := hA
  refine ⟨c / 2, by positivity, ?_⟩
  have hev : ∀ᶠ N in atTop, 2 * ((B : ℝ) + 1) ≤ c * (Nat.primeCounting N : ℝ) := by
    have ht : Tendsto (fun N => (Nat.primeCounting N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
    filter_upwards [ht.eventually_ge_atTop (2 * ((B : ℝ) + 1) / c)] with N hN
    rw [div_le_iff₀ hc] at hN
    linarith
  refine (hfreq.and_eventually hev).mono fun N ⟨h1, h2⟩ => ?_
  have hsub : (Finset.range (N + 1)).filter (· ∈ A) ⊆
      (Finset.range (N + 1)).filter (· ∈ A ∩ {p | B < p}) ∪ Finset.range (B + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Set.mem_inter_iff,
      Set.mem_ofPred_eq] at hp ⊢
    by_cases hpB : B < p
    · exact Or.inl ⟨hp.1, hp.2, hpB⟩
    · exact Or.inr (by omega)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_range] at hcard
  have hcard' : ((((Finset.range (N + 1)).filter (· ∈ A)).card : ℕ) : ℝ) ≤
      (((Finset.range (N + 1)).filter (· ∈ A ∩ {p | B < p})).card : ℝ) + (B + 1) := by
    exact_mod_cast hcard
  have hhalf : c / 2 * (Nat.primeCounting N : ℝ) = c * (Nat.primeCounting N : ℝ) / 2 := by ring
  rw [hhalf]
  have key : c * (Nat.primeCounting N : ℝ) / 2 ≤
      (((Finset.range (N + 1)).filter (· ∈ A ∩ {p | B < p})).card : ℝ) := by
    linarith
  convert key using 3
  ext x; simp

/-- Theorem 1.2 plus positive relative upper density of `G` gives the shape of
`ZInQ.GoodPrimeAP`: for every `K`, a progression `x + j v` (`j ≤ K`, `x, v ≥ 1`) in `G` above
every element of the finite set `S`. -/
theorem progressions_above_of_greenTaoDense (hGT : GreenTaoDense) {G : ℕ → Prop}
    (hGprime : ∀ p, G p → p.Prime) (hG : PrimesRelUpperDensityPos {p | G p}) (S : Finset ℕ) :
    ∀ K : ℕ, ∃ x v : ℕ, 1 ≤ x ∧ 1 ≤ v ∧ ∀ j ≤ K, G (x + j * v) ∧ ∀ q ∈ S, q < x + j * v := by
  intro K
  set B := S.sup id
  have hAP := hGT ({p | G p} ∩ {p | B < p}) (fun p hp => hGprime p hp.1) (hG.diff_le B) (K + 1)
  obtain ⟨a, b, hb, hab⟩ := hAP
  have ha0 := hab 0 (Nat.succ_pos K)
  simp only [mul_zero, add_zero, Set.mem_inter_iff, Set.mem_ofPred_eq] at ha0
  refine ⟨a, b, (hGprime a ha0.1).one_lt.le, hb, fun j hj => ?_⟩
  have h := hab j (Nat.lt_succ_of_le hj)
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at h
  rw [mul_comm j b]
  refine ⟨h.1, fun q hq => lt_of_le_of_lt ?_ h.2⟩
  exact Finset.le_sup (f := id) hq

end GTSearch
