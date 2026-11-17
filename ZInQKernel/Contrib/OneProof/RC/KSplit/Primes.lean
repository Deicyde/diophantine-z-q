import Mathlib

/-!
# Lane RC3: the simultaneous prime conditions of the nonempty K-split seed

Manuscript `diophantine_zq.tex`, Lemma `ex:sec7-ksplit-seed` (tex 2643–2645) and Proposition
`ex:app-nonempty-seeds` (tex 10482–10488). For `ℓ` odd squarefree `> 1` and `k` odd squarefree
with a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ` (a prime ramified in `K = ℚ(√k)` outside the ramification of
`ℚ(i, √ℓ)`), there are arbitrarily large primes `p ≡ 1 (mod 4)` with `(ℓ/p) = −1` and
`(k/p) = 1`.

The manuscript sentence (tex 10482–10488): "Choose `p` also with `(k/p) = 1`, `p ≡ 1 (mod 4)` and
`(ℓ/p) = −1`, outside the finite support. These prescriptions are compatible: `K` has a ramified
prime outside the ramification of `ℚ(i, √ℓ)`, so `K ∩ ℚ(i, √ℓ) = ℚ`. The corresponding quadratic
residue classes are therefore nonempty and Dirichlet's theorem supplies infinitely many such
primes."

This file is the elementary (CRT) form of that field-intersection sentence.
DEPARTURE (form only): the linear disjointness `K ∩ ℚ(i, √ℓ) = ℚ` is used in its character form
at the fresh prime `q₀` (CRT), with the same input (a ramified prime of `K` outside `2ℓ`) and the
same conclusion.

## The argument

1. Let `q₁` be a prime factor of `ℓ` (odd, as `ℓ` is odd); `q₀ ≠ q₁` since `q₀ ∤ ℓ`.
2. On the odd primes `Q = supp ℓ ∪ supp k` prescribe the symbols `(p/q)`: `−1` at `q₁`; at `q₀`,
   `−1` if `q₁ ∣ k` and `+1` otherwise; `+1` at every other `q ∈ Q`.
3. The Chinese remainder theorem (modulus `4 ∏ Q`) and Dirichlet's theorem give a prime `p > n`
   with `p ≡ 1 (mod 4)` realizing these symbols (`exists_residue_jacobiSym`,
   `exists_prime_gt_one_mod_four_of_modEq`).
4. As `p ≡ 1 (mod 4)`, `(q/p) = (p/q)` for every odd prime `q` and `(−1/p) = 1`; by
   multiplicativity, `(ℓ/p) = ∏_{q ∣ ℓ} (p/q) = −1` (only `q₁` contributes) and
   `(k/p) = ∏_{q ∣ k} (p/q) = 1` (the factors at `q₀` and, if `q₁ ∣ k`, at `q₁` cancel).

## Main results

* `exists_prime_seed_conditions`: the seed conditions for `ℓ` odd squarefree `> 1`.
* `exists_prime_seed_conditions_of_mod_twelve`: the same for the manuscript's `ℓ ≡ 11 (mod 12)`.

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.KSplit

/-- **A residue with a prescribed quadratic character** modulo an odd prime `q` (`PROVED`;
tex 10482–10488: "The corresponding quadratic residue classes are therefore nonempty"): for
`s = ±1` there is `a` prime to `q` with `(a/q) = s`. -/
theorem exists_residue_jacobiSym {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {s : ℤ}
    (hs : s = 1 ∨ s = -1) : ∃ a : ℕ, ¬ q ∣ a ∧ jacobiSym (a : ℤ) q = s := by
  have := Fact.mk hq
  rcases hs with rfl | rfl
  · exact ⟨1, fun h => hq.one_lt.ne' (Nat.dvd_one.mp h), by simp⟩
  · obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
    refine ⟨x.val, fun h => hx ?_, ?_⟩
    · have h0 : (x.val : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [ZMod.natCast_zmod_val] at h0
      rw [h0]; exact ⟨0, by simp⟩
    · rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff']
      simpa using hx

/-- **CRT and Dirichlet** (`PROVED`; tex 10482–10488: "Dirichlet's theorem supplies infinitely
many such primes"): given residues `a q` prime to `q` modulo the odd primes `q` of a finite set
`Q`, there are arbitrarily large primes `p ≡ 1 (mod 4)` with `p ≡ a q (mod q)` for all `q ∈ Q`.
The residues are glued by the Chinese remainder theorem into a reduced class modulo `4 ∏ Q`, which
contains arbitrarily large primes by Dirichlet's theorem. -/
theorem exists_prime_gt_one_mod_four_of_modEq (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2)
    (a : ℕ → ℕ) (ha : ∀ q ∈ Q, ¬ q ∣ a q) (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p % 4 = 1 ∧ ∀ q ∈ Q, p ≡ a q [MOD q] := by
  classical
  have hs : ∀ q ∈ Q, id q ≠ 0 := fun q hq => (hQ q hq).1.ne_zero
  have pp : Set.Pairwise (Q : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro q hq q' hq' hne
    exact (Nat.coprime_primes (hQ q hq).1 (hQ q' hq').1).mpr hne
  obtain ⟨k₁, hk₁⟩ := Nat.chineseRemainderOfFinset a id Q hs pp
  set N := ∏ q ∈ Q, q with hN
  have hcop4 : Nat.Coprime 4 N := by
    refine Nat.Coprime.prod_right fun q hq => ?_
    have hqp := (hQ q hq).1
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hqp]
    intro h
    have h2 : q ∣ 2 := hqp.dvd_of_dvd_pow (show q ∣ 2 ^ 2 by simpa using h)
    exact (hQ q hq).2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp h2)
  obtain ⟨k, hk4, hkN⟩ := Nat.chineseRemainder hcop4 1 k₁
  have hkq : ∀ q ∈ Q, k ≡ a q [MOD q] := fun q hq =>
    (Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem _ hq) hkN).trans (hk₁ q hq)
  have hkcop : Nat.Coprime k (4 * N) := by
    refine Nat.Coprime.mul_right ?_ (Nat.Coprime.prod_right fun q hq => ?_)
    · show Nat.gcd k 4 = 1
      rw [Nat.ModEq.gcd_eq hk4]; rfl
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hQ q hq).1]
      intro h
      exact ha q hq (Nat.modEq_zero_iff_dvd.mp
        ((hkq q hq).symm.trans (Nat.modEq_zero_iff_dvd.mpr h)))
  have hpos : 0 < 4 * N :=
    Nat.mul_pos (by norm_num) (Finset.prod_pos fun q hq => (hQ q hq).1.pos)
  have : NeZero (4 * N) := ⟨hpos.ne'⟩
  obtain ⟨p, hpn, hp, hpk⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime k (4 * N)).mpr hkcop) n
  have hpk' : p ≡ k [MOD 4 * N] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hpk
  refine ⟨p, hpn, hp, ?_, fun q hq => ?_⟩
  · exact (Nat.ModEq.of_dvd (Dvd.intro N rfl) hpk').trans hk4
  · exact (Nat.ModEq.of_dvd ((Finset.dvd_prod_of_mem _ hq).trans (Dvd.intro_left 4 rfl))
      hpk').trans (hkq q hq)

/-- **The simultaneous prime conditions of the nonempty K-split seed** (Lane RC3; manuscript
`diophantine_zq.tex`, Lemma `ex:sec7-ksplit-seed`, tex 2643–2645, and Proposition
`ex:app-nonempty-seeds`, tex 10482–10488): for `ℓ` odd squarefree `> 1` and `k` odd squarefree
with a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ` (a prime ramified in `K = ℚ(√k)` outside the ramification of
`ℚ(i, √ℓ)`), there are arbitrarily large primes `p ≡ 1 (mod 4)` with `(ℓ/p) = −1` and `(k/p) = 1`.
(For a prime `p` the Jacobi symbol is the Legendre symbol.) `PROVED`, in the elementary (CRT) form
of the manuscript's argument: the prescriptions `(p/q₁) = −1` at a prime `q₁ ∣ ℓ`,
`(p/q₀) = −1` or `+1` at the fresh prime `q₀` according as `q₁ ∣ k` or not, and `(p/q) = +1` at
the other primes of `ℓk` are realized by CRT and Dirichlet, and reciprocity turns them into
`(ℓ/p) = −1`, `(k/p) = 1` (DEPARTURE, form only: the character form of `K ∩ ℚ(i, √ℓ) = ℚ`). -/
theorem exists_prime_seed_conditions {ℓ : ℕ} (hℓ_odd : Odd ℓ) (hℓ_one : 1 < ℓ)
    (hℓ_sf : Squarefree ℓ) {k : ℤ} (hk_odd : Odd k) (hk_sf : Squarefree k)
    {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k) (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p % 4 = 1 ∧ jacobiSym (ℓ : ℤ) p = -1 ∧ jacobiSym k p = 1 := by
  classical
  -- step 1: a prime `q₁ ∣ ℓ`; `q₁ ≠ q₀` since `q₀ ∤ ℓ`
  obtain ⟨q₁, hq₁, hq₁ℓ⟩ := Nat.exists_prime_and_dvd (show ℓ ≠ 1 by omega)
  have hℓ0 : ℓ ≠ 0 := by omega
  have hq₀ℓ' : ¬ q₀ ∣ ℓ := fun h => hq₀ℓ (Dvd.dvd.mul_left h 2)
  have hq₀₁ : q₀ ≠ q₁ := by rintro rfl; exact hq₀ℓ' hq₁ℓ
  -- `|k|` is odd and squarefree, and `q₀ ∣ |k|`
  have hm_odd : Odd k.natAbs := Int.natAbs_odd.mpr hk_odd
  have hm_sf : Squarefree k.natAbs := Int.squarefree_natAbs.mpr hk_sf
  have hm0 : k.natAbs ≠ 0 := fun h => by rw [h] at hm_odd; exact Nat.not_odd_zero hm_odd
  have hq₀m : q₀ ∣ k.natAbs := Int.natCast_dvd.mp hq₀k
  -- step 2: the prescribed symbols `σ q = (p/q)`
  obtain ⟨σ, hσ₁, hσ₀, hσ, hσpm⟩ : ∃ σ : ℕ → ℤ, σ q₁ = -1 ∧
      σ q₀ = (if q₁ ∣ k.natAbs then -1 else 1) ∧
      (∀ q, q ≠ q₁ → q ≠ q₀ → σ q = 1) ∧ (∀ q, σ q = 1 ∨ σ q = -1) := by
    refine ⟨fun q => if q = q₁ then -1 else if q = q₀ then (if q₁ ∣ k.natAbs then -1 else 1)
      else 1, by simp, by simp [hq₀₁], fun q h1 h0 => by simp [h1, h0], fun q => ?_⟩
    dsimp only
    split_ifs <;> simp
  set Q := ℓ.primeFactors ∪ k.natAbs.primeFactors with hQ_def
  have hodd : ∀ {N : ℕ}, Odd N → ∀ q ∈ N.primeFactors, q.Prime ∧ q ≠ 2 := by
    intro N hN q hq
    refine ⟨Nat.prime_of_mem_primeFactors hq, ?_⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hq))
  have hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2 := by
    intro q hq
    rcases Finset.mem_union.mp hq with h | h
    · exact hodd hℓ_odd q h
    · exact hodd hm_odd q h
  have hres : ∀ q ∈ Q, ∃ a : ℕ, ¬ q ∣ a ∧ jacobiSym (a : ℤ) q = σ q := fun q hq =>
    exists_residue_jacobiSym (hQ q hq).1 (hQ q hq).2 (hσpm q)
  choose! a ha using hres
  -- step 3: CRT and Dirichlet
  obtain ⟨p, hpn, hp, hp4, hpa⟩ :=
    exists_prime_gt_one_mod_four_of_modEq Q hQ a (fun q hq => (ha q hq).1) n
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
  -- step 4: reciprocity, `(q/p) = (p/q) = σ q` for `q ∈ Q`
  have hJ : ∀ q ∈ Q, legendreSym p (q : ℤ) = σ q := by
    intro q hq
    have := Fact.mk (hQ q hq).1
    rw [← legendreSym.quadratic_reciprocity_one_mod_four hp4 (hQ q hq).2,
      jacobiSym.legendreSym.to_jacobiSym, ← (ha q hq).2]
    apply jacobiSym.mod_left'
    exact_mod_cast hpa q hq
  -- multiplicativity over the primes of a squarefree `N` with support in `Q`
  have hmul : ∀ N : ℕ, Squarefree N → N.primeFactors ⊆ Q →
      legendreSym p (N : ℤ) = ∏ q ∈ N.primeFactors, σ q := by
    intro N hN hNQ
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hN]
    rw [Nat.cast_prod, ← legendreSym.hom_apply, map_prod]
    exact Finset.prod_congr rfl fun q hq => by rw [legendreSym.hom_apply, hJ q (hNQ hq)]
  refine ⟨p, hpn, hp, hp4, ?_, ?_⟩
  · -- `(ℓ/p) = −1`: only `q₁` contributes
    rw [← jacobiSym.legendreSym.to_jacobiSym, hmul ℓ hℓ_sf Finset.subset_union_left,
      Finset.prod_eq_single_of_mem q₁ (Nat.mem_primeFactors.mpr ⟨hq₁, hq₁ℓ, hℓ0⟩) ?_, hσ₁]
    intro q hq hne
    exact hσ q hne fun h => hq₀ℓ' (h ▸ Nat.dvd_of_mem_primeFactors hq)
  · -- `(k/p) = (|k|/p)` since `(−1/p) = 1`
    have hkm : legendreSym p k = legendreSym p (k.natAbs : ℤ) := by
      rcases Int.natAbs_eq k with h | h
      · rw [← h]
      · conv_lhs => rw [h]
        rw [neg_eq_neg_one_mul, legendreSym.mul, legendreSym.at_neg_one hp2,
          ZMod.χ₄_nat_one_mod_four hp4, one_mul]
    rw [← jacobiSym.legendreSym.to_jacobiSym, hkm, hmul _ hm_sf Finset.subset_union_right]
    have hq₀mem : q₀ ∈ k.natAbs.primeFactors := Nat.mem_primeFactors.mpr ⟨hq₀, hq₀m, hm0⟩
    by_cases h1 : q₁ ∣ k.natAbs
    · -- the factors at `q₁` and `q₀` cancel
      rw [Finset.prod_eq_mul_of_mem q₁ q₀ (Nat.mem_primeFactors.mpr ⟨hq₁, h1, hm0⟩) hq₀mem
        hq₀₁.symm (fun c _ hc => hσ c hc.1 hc.2), hσ₁, hσ₀, ite_eq_left h1]
      norm_num
    · -- every factor is `+1`
      rw [Finset.prod_eq_single_of_mem q₀ hq₀mem ?_, hσ₀, ite_eq_right h1]
      intro c hc hc0
      exact hσ c (fun h => h1 (h ▸ Nat.dvd_of_mem_primeFactors hc)) hc0

/-- **The seed conditions for the manuscript's `ℓ ≡ 11 (mod 12)`** (Lane RC3; `PROVED`; manuscript
`diophantine_zq.tex`, Lemma `ex:sec7-ksplit-seed`, tex 2643–2645, and Proposition
`ex:app-nonempty-seeds`, tex 10482–10488): `exists_prime_seed_conditions`, with `ℓ` odd and
`ℓ > 1` read off from `ℓ ≡ 11 (mod 12)`. -/
theorem exists_prime_seed_conditions_of_mod_twelve {ℓ : ℕ} (hℓ_pos : 0 < ℓ) (hℓ_sf : Squarefree ℓ)
    (hℓ12 : ℓ % 12 = 11) {k : ℤ} (hk_odd : Odd k) (hk_sf : Squarefree k)
    {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k) (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p % 4 = 1 ∧ jacobiSym (ℓ : ℤ) p = -1 ∧ jacobiSym k p = 1 :=
  exists_prime_seed_conditions (Nat.odd_iff.mpr (by omega)) (by omega) hℓ_sf hk_odd hk_sf hq₀
    hq₀k hq₀ℓ n

end ZInQ.Manuscript.RC.KSplit
