import Mathlib

/-!
# RankCounts: places of a quadratic field over the rational primes (for (5.1))

The proof of Lemma `ex:limits-residual-bound` (`diophantine_zq.tex`, tex 4453–4648) counts places
of the imaginary quadratic field `K = ℚ(√k)`:

* tex 4469–4470: `T` is the set of rational primes below `S₀` "together with the primes ramified in
  `K/ℚ`", and (5.1a) `s ≤ v + A + 1 + j` uses that a ramified prime is `2` or divides `k`;
* tex 4481: `r` is the number of finite rational primes ramified in `K`;
* tex 4516–4517: "The bound on `|S_T|` counts one prime over each ramified rational prime and at most
  two over each other prime."

Lane RC6 (`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`, draft commit `7481834f`)
takes these three facts as GLUE fields of the structure `ResidualRankCounts`, verbatim:

```
  /-- GLUE (tex 4470): ramified primes divide `4k` -/
  ram_sub : Ram ⊆ k.natAbs.primeFactors ∪ {2}
  /-- GLUE: at most two places over each rational prime (tex 4517) -/
  nPlaces_le_two : ∀ p ∈ primeSetT N r D Ram, nPlaces p ≤ 2
  /-- GLUE: one place over each ramified prime (tex 4516) -/
  nPlaces_ram : ∀ p ∈ Ram, nPlaces p = 1
```

This file proves them over genuine Mathlib objects, so they become PROVED: `nPlaces K p` is the
number of prime ideals of `𝓞 K` lying over `p ℤ` (`nPlaces`), and `p` is ramified when some prime
of `𝓞 K` over `p` has ramification index at least two (`IsRamifiedPrime`).

Encoding of `K = ℚ(√k)` (`IsQuadraticRadicand K k α`): `[K : ℚ] = 2`, and `α ∈ 𝓞 K` satisfies
`α² = k` and generates `K` over `ℚ`. Only the count of places needs `[K : ℚ] = 2` alone; the
statement on ramified primes uses `α`.

Proofs: the fundamental identity `∑_{𝔓 ∣ p} e(𝔓) f(𝔓) = [K : ℚ] = 2` (Mathlib
`Ideal.sum_ramification_inertia_eq_finrank`) gives at most two primes over `p`, and only one when
some `e(𝔓) ≥ 2`. A ramified `𝔓` divides the different ideal (`not_dvd_differentIdeal_iff`), which
contains `f'(α) = 2α` for the minimal polynomial `f = X² - k` (`aeval_derivative_mem_differentIdeal`);
hence `4k = (2α)² ∈ 𝔓 ∩ ℤ = pℤ`, so `p = 2` or `p ∣ k`.

Kinds: every node below is PROVED. Nothing is assumed.
-/

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open NumberField Polynomial

section Defs

variable (K : Type) [Field K] [NumberField K]

/-- The prime ideals of `𝓞 K` lying over the rational prime `p` (the finite places of `K` above
`p`, tex 4486, 4516). -/
abbrev primesAbove (p : ℕ) : Set (Ideal (𝓞 K)) := (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)

/-- The number of places of `K` above the rational prime `p` (RC6's `nPlaces`, tex 4516–4517). -/
noncomputable def nPlaces (p : ℕ) : ℕ := (primesAbove K p).ncard

/-- `p` is ramified in `K`: some prime of `𝓞 K` above `p` has ramification index at least two
(tex 4470, 4481). -/
def IsRamifiedPrime (p : ℕ) : Prop := ∃ P ∈ primesAbove K p, 2 ≤ P.ramificationIdx ℤ

/-- `K = ℚ(√k)` with `√k = α`: `[K : ℚ] = 2`, `α ∈ 𝓞 K`, `α² = k`, and `α` generates `K` over `ℚ`. -/
def IsQuadraticRadicand (k : ℤ) (α : 𝓞 K) : Prop :=
  Module.finrank ℚ K = 2 ∧ α ^ 2 = (k : 𝓞 K) ∧ Algebra.adjoin ℚ {(α : K)} = ⊤

end Defs

section Counting

variable {K : Type} [Field K] [NumberField K]

lemma primesAbove_finite (p : ℕ) : (primesAbove K p).Finite :=
  Algebra.QuasiFinite.finite_primesOver _

omit [NumberField K] in
lemma nPlaces_eq_card (p : ℕ) [Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K))] :
    nPlaces K p = Fintype.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := by
  rw [nPlaces, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

/-- Every term `e(𝔓) f(𝔓)` of the fundamental identity is at least one. -/
lemma one_le_ramificationIdx_mul_inertiaDeg (P : Ideal (𝓞 K)) [P.IsPrime] :
    1 ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
  Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Ideal.ramificationIdx_pos ℤ P).ne' (Ideal.inertiaDeg_pos P ℤ).ne')

/-- The fundamental identity `∑_{𝔓 ∣ p} e f = [K : ℚ] = 2` at a prime ideal `p ℤ` of `ℤ`. -/
lemma sum_ramificationIdx_mul_inertiaDeg {p : ℕ} (hK : Module.finrank ℚ K = 2)
    [(Ideal.span {(p : ℤ)}).IsPrime] [Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K))] :
    ∑ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 2 := by
  rw [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank, hK]

/-- If `p ℤ` is not a prime ideal (`p ≠ 0` not prime), no prime of `𝓞 K` lies over it. -/
lemma nPlaces_eq_zero_of_not_isPrime {p : ℕ} (hp : ¬ (Ideal.span {(p : ℤ)}).IsPrime) :
    nPlaces K p = 0 := by
  rw [nPlaces, Set.ncard_eq_zero (primesAbove_finite p)]
  ext P
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hP, hlies⟩
  exact hp (hlies.over ▸ Ideal.IsPrime.comap (algebraMap ℤ (𝓞 K)))

/-- **At most two places of a quadratic field over each rational prime** (tex 4516–4517). -/
theorem nPlaces_le_two_of_finrank (hK : Module.finrank ℚ K = 2) (p : ℕ) : nPlaces K p ≤ 2 := by
  by_cases hp : (Ideal.span {(p : ℤ)}).IsPrime
  · have := (primesAbove_finite (K := K) p).fintype
    rw [nPlaces_eq_card p, ← sum_ramificationIdx_mul_inertiaDeg (p := p) hK, Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun q _ => one_le_ramificationIdx_mul_inertiaDeg q.1
  · rw [nPlaces_eq_zero_of_not_isPrime hp]; omega

/-- **One place of a quadratic field over each ramified rational prime** (tex 4516). -/
theorem nPlaces_eq_one_of_isRamifiedPrime (hK : Module.finrank ℚ K = 2) {p : ℕ}
    (hram : IsRamifiedPrime K p) : nPlaces K p = 1 := by
  have := (primesAbove_finite (K := K) p).fintype
  obtain ⟨P, hP, he⟩ := hram
  have hPprime : P.IsPrime := hP.1
  have hpprime : (Ideal.span {(p : ℤ)}).IsPrime :=
    hP.2.over ▸ Ideal.IsPrime.comap (algebraMap ℤ (𝓞 K))
  set Q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := ⟨P, hP⟩
  have hsum := sum_ramificationIdx_mul_inertiaDeg (K := K) (p := p) hK
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ Q)] at hsum
  have hQ : 2 ≤ Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ :=
    le_trans he (Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos P ℤ))
  have hrest : (Finset.univ.erase Q).card ≤
      ∑ q ∈ Finset.univ.erase Q, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun q _ => one_le_ramificationIdx_mul_inertiaDeg q.1
  have hcard := Finset.card_erase_of_mem (Finset.mem_univ Q)
  rw [Finset.card_univ] at hcard
  have hpos : 0 < Fintype.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :=
    Fintype.card_pos_iff.mpr ⟨Q⟩
  rw [nPlaces_eq_card p]
  omega

end Counting

section Ramified

variable {K : Type} [Field K] [NumberField K]

lemma natDegree_minpoly_rat (hK : Module.finrank ℚ K = 2) (α : 𝓞 K)
    (hgen : Algebra.adjoin ℚ {(α : K)} = ⊤) : (minpoly ℚ (α : K)).natDegree = 2 := by
  have hint : IsIntegral ℚ (α : K) := .of_finite ℚ _
  rw [← IntermediateField.adjoin.finrank hint, ← hK]
  have : IntermediateField.adjoin ℚ {(α : K)} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.adjoin_toSubalgebra, hgen,
      IntermediateField.top_toSubalgebra]
  rw [this, IntermediateField.finrank_top']

/-- The minimal polynomial of `√k` over `ℤ` is `X² - k`. -/
lemma minpoly_eq_X_sq_sub (k : ℤ) (α : 𝓞 K) (h : IsQuadraticRadicand K k α) :
    minpoly ℤ α = X ^ 2 - C k := by
  obtain ⟨hK, hα, hgen⟩ := h
  have hint : IsIntegral ℤ α := RingOfIntegers.isIntegral α
  have hmon : (X ^ 2 - C k : ℤ[X]).Monic := monic_X_pow_sub_C k two_ne_zero
  have hdvd : minpoly ℤ α ∣ X ^ 2 - C k := by
    apply minpoly.isIntegrallyClosed_dvd hint
    rw [map_sub, map_pow, aeval_X, aeval_C, hα]
    simp
  have hdeg : (minpoly ℤ α).natDegree = 2 := by
    rw [← natDegree_minpoly_rat hK α hgen]
    change _ = (minpoly ℚ (algebraMap (𝓞 K) K α)).natDegree
    rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hint,
      natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int]
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd ?_
  rw [hdeg, natDegree_X_pow_sub_C]

/-- The radicand is nonzero. -/
lemma radicand_ne_zero (k : ℤ) (α : 𝓞 K) (h : IsQuadraticRadicand K k α) : k ≠ 0 := by
  obtain ⟨hK, hα, hgen⟩ := h
  rintro rfl
  have h0 : α = 0 := by simpa using hα
  have hd := natDegree_minpoly_rat hK α hgen
  rw [h0, show ((0 : 𝓞 K) : K) = 0 from rfl, minpoly.zero, natDegree_X] at hd
  exact absurd hd (by norm_num)

/-- `f'(√k) = 2√k` lies in the different ideal of `𝓞 K / ℤ`. -/
lemma two_mul_mem_differentIdeal (k : ℤ) (α : 𝓞 K) (h : IsQuadraticRadicand K k α) :
    2 * α ∈ differentIdeal ℤ (𝓞 K) := by
  have hd := aeval_derivative_mem_differentIdeal ℤ ℚ (L := K) α h.2.2
  rw [minpoly_eq_X_sq_sub k α h] at hd
  have h2 : (aeval α) (2 : ℤ[X]) = 2 := by
    rw [show (2 : ℤ[X]) = C 2 from rfl, aeval_C]; simp
  simpa [derivative_X_pow, h2] using hd

/-- A prime of `𝓞 K` with ramification index at least two divides the different ideal. -/
lemma dvd_differentIdeal_of_two_le (P : Ideal (𝓞 K)) [P.IsPrime]
    (he : 2 ≤ P.ramificationIdx ℤ) : P ∣ differentIdeal ℤ (𝓞 K) := by
  by_contra hP
  have := (not_dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 K)).mp hP
  have h1 := Ideal.ramificationIdx_eq_one P ℤ
  omega

/-- **A prime ramified in `ℚ(√k)` is `2` or divides `k`** (tex 4470). -/
theorem mem_primeFactors_of_isRamifiedPrime (k : ℤ) (α : 𝓞 K) (h : IsQuadraticRadicand K k α)
    {p : ℕ} (hram : IsRamifiedPrime K p) : p ∈ k.natAbs.primeFactors ∪ {2} := by
  obtain ⟨P, ⟨hPprime, hlies⟩, he⟩ := hram
  have hle : differentIdeal ℤ (𝓞 K) ≤ P :=
    Ideal.dvd_iff_le.mp (dvd_differentIdeal_of_two_le P he)
  have h2 : 2 * α ∈ P := hle (two_mul_mem_differentIdeal k α h)
  have h4 : algebraMap ℤ (𝓞 K) (4 * k) ∈ P := by
    have : (2 * α) ^ 2 = algebraMap ℤ (𝓞 K) (4 * k) := by
      rw [mul_pow, h.2.1]; simp; norm_num
    rw [← this]; exact Ideal.pow_mem_of_mem P h2 2 two_pos
  have hmem : (4 * k : ℤ) ∈ Ideal.span {(p : ℤ)} := by
    rw [Ideal.over_def P (Ideal.span {(p : ℤ)})]
    exact h4
  -- `p ≠ 0`: over `0` lies only `⊥`, which is unramified.
  have hp0 : p ≠ 0 := by
    rintro rfl
    have hbot : P.under ℤ = ⊥ := by
      rw [← Ideal.over_def P (Ideal.span {((0 : ℕ) : ℤ)})]; simp
    have hPbot : P = ⊥ := Ideal.eq_bot_of_under_eq_bot hbot
    subst hPbot
    rw [Ideal.ramificationIdx_bot_eq_one] at he
    omega
  have hpprime : (Ideal.span {(p : ℤ)}).IsPrime :=
    hlies.over ▸ Ideal.IsPrime.comap (algebraMap ℤ (𝓞 K))
  have hpZ : Prime (p : ℤ) := (Ideal.span_singleton_prime (by exact_mod_cast hp0)).mp hpprime
  have hp : p.Prime := Nat.prime_iff_prime_int.mpr hpZ
  rw [Ideal.mem_span_singleton] at hmem
  rcases hpZ.dvd_or_dvd hmem with hd | hd
  · have h2' : (p : ℤ) ∣ 2 := hpZ.dvd_of_dvd_pow (n := 2) (by norm_num [hd])
    have : p ∣ 2 := by exact_mod_cast h2'
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    simp [this]
  · apply Finset.mem_union_left
    rw [Nat.mem_primeFactors]
    exact ⟨hp, Int.natCast_dvd.mp hd, Int.natAbs_ne_zero.mpr (radicand_ne_zero k α h)⟩

end Ramified

/-! ### The nodes -/

/-- **RankCounts node `QuadraticPlacesLeTwo`** (tex 4516–4517, in the proof of
`ex:limits-residual-bound`: "at most two [places] over each other prime"). PROVED.

For a quadratic number field `K`, every rational prime `p` has at most two prime ideals of `𝓞 K`
above it. Discharges RC6's GLUE field
`nPlaces_le_two : ∀ p ∈ primeSetT N r D Ram, nPlaces p ≤ 2` of `ResidualRankCounts`
(`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`, draft commit `7481834f`) with
`nPlaces := nPlaces K` (it holds for every natural number `p`). -/
def QuadraticPlacesLeTwo : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ p : ℕ, nPlaces K p ≤ 2

theorem quadraticPlacesLeTwo_proof : QuadraticPlacesLeTwo :=
  fun _ _ _ hK p => nPlaces_le_two_of_finrank hK p

/-- **RankCounts node `QuadraticRamifiedOnePlace`** (tex 4516, in the proof of
`ex:limits-residual-bound`: "one prime over each ramified rational prime"). PROVED.

For a quadratic number field `K`, a rational prime ramified in `K` has exactly one prime of `𝓞 K`
above it. Discharges RC6's GLUE field `nPlaces_ram : ∀ p ∈ Ram, nPlaces p = 1` of
`ResidualRankCounts` (`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`, draft commit
`7481834f`) with `nPlaces := nPlaces K`, for any `Ram` consisting of ramified primes. -/
def QuadraticRamifiedOnePlace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ p : ℕ, IsRamifiedPrime K p → nPlaces K p = 1

theorem quadraticRamifiedOnePlace_proof : QuadraticRamifiedOnePlace :=
  fun _ _ _ hK _ hram => nPlaces_eq_one_of_isRamifiedPrime hK hram

/-- **RankCounts node `QuadraticRamifiedDvdTwoK`** (tex 4469–4470 and (5.1a), tex 4471–4474, in the
proof of `ex:limits-residual-bound`: the primes ramified in `K = ℚ(√k)` are counted by `ω(k)` once
`2 ∈ T`). PROVED.

A rational prime ramified in `ℚ(√k)` is `2` or divides `k`. Discharges RC6's GLUE field
`ram_sub : Ram ⊆ k.natAbs.primeFactors ∪ {2}` ("ramified primes divide `4k`") of
`ResidualRankCounts` (`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`, draft commit
`7481834f`), pointwise; see `rc6RamifiedFields_proof` for the field shape. -/
def QuadraticRamifiedDvdTwoK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K), IsQuadraticRadicand K k α →
    ∀ p : ℕ, IsRamifiedPrime K p → p ∈ k.natAbs.primeFactors ∪ {2}

theorem quadraticRamifiedDvdTwoK_proof : QuadraticRamifiedDvdTwoK :=
  fun _ _ _ k α h _ hram => mem_primeFactors_of_isRamifiedPrime k α h hram

/-- **RankCounts node `RC6RamifiedFields`**: the three GLUE fields `ram_sub`, `nPlaces_le_two`,
`nPlaces_ram` of RC6's `ResidualRankCounts` (tex 4470, 4516–4517), in their Lean shape, for
`K = ℚ(√k)`, `nPlaces := nPlaces K`, any finite set `Ram` of ramified primes, and any finite set
`T` of naturals (in RC6, `T = primeSetT N r D Ram`). Source of the field texts:
`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`, draft commit `7481834f`. PROVED. -/
def RC6RamifiedFields : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K), IsQuadraticRadicand K k α →
    ∀ (Ram T : Finset ℕ), (∀ p ∈ Ram, IsRamifiedPrime K p) →
      Ram ⊆ k.natAbs.primeFactors ∪ {2} ∧ (∀ p ∈ T, nPlaces K p ≤ 2) ∧
        (∀ p ∈ Ram, nPlaces K p = 1)

theorem rc6RamifiedFields_proof : RC6RamifiedFields := by
  intro K _ _ k α h Ram T hRam
  exact ⟨fun p hp => mem_primeFactors_of_isRamifiedPrime k α h (hRam p hp),
    fun p _ => nPlaces_le_two_of_finrank h.1 p,
    fun p hp => nPlaces_eq_one_of_isRamifiedPrime h.1 (hRam p hp)⟩

/-! ### The finite set of ramified primes -/

open Classical in
/-- The set of rational primes ramified in `K = ℚ(√k)`, as a `Finset` (it is contained in the
primes dividing `2k`). A genuine choice for RC6's `Ram`. -/
noncomputable def ramifiedPrimes (K : Type) [Field K] [NumberField K] (k : ℤ) : Finset ℕ :=
  (k.natAbs.primeFactors ∪ {2}).filter (IsRamifiedPrime K)

/-- **RankCounts node `RamifiedPrimesSpec`** (tex 4470, 4481). PROVED. For `K = ℚ(√k)`, membership
in `ramifiedPrimes K k` is exactly ramification in `K`; so `Ram := ramifiedPrimes K k` is the set
of ramified primes of tex 4470 (and `r = |Ram|` of tex 4481). -/
def RamifiedPrimesSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K), IsQuadraticRadicand K k α →
    ∀ p : ℕ, p ∈ ramifiedPrimes K k ↔ IsRamifiedPrime K p

theorem ramifiedPrimesSpec_proof : RamifiedPrimesSpec := by
  intro K _ _ k α h p
  classical
  unfold ramifiedPrimes
  rw [Finset.mem_filter]
  exact ⟨fun hp => hp.2, fun hp => ⟨mem_primeFactors_of_isRamifiedPrime k α h hp, hp⟩⟩

end ZInQ.Contrib.CloudB3RC53.RankCounts
