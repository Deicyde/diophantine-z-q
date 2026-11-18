import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalCommon
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

/-!
# GenusOdd: regrouping an Euler product over the primes of `K` by rational primes (PROVED)

For a number field `K`, Euler products over the primes `𝔭` of `K` of factors `f_𝔭(N𝔭^{-s})`
(Mathlib's `ArithmeticFunction.eulerProduct` of `ofPowerSeries`, as in CST's `twistedLFunction`)
are computed prime by prime:

* `natCard_residueField_adicCompletionIntegers`: the residue field of `𝓞_{K_𝔭}` has `N𝔭` elements
  (Tau Ceti's `residueFieldEquivAdicCompletionIntegers`);
* `northcott_natCard_residueField_K`: finitely many `𝔭` of bounded residue cardinality;
* `primesAbove_finite`, `primesAboveFinset`: the primes above `p` form a finite set;
* `eulerProduct_apply_prime_pow`: the value at `p ^ k` only sees the finitely many `𝔭 ∣ p`;
* `isMultiplicative_eulerProduct_ofPowerSeries`: the Euler product is multiplicative;
* `mul_apply_prime_pow_congr`: a Dirichlet convolution at `p ^ k` only sees values at `p ^ j`;
* `twistedLFunction_eq_eulerProduct`, `constantCoeff_twistFactor`: CST's twisted `L`-function is
  such an Euler product, with factors of constant coefficient `1`.

All results here are `PROVED`.
-/

noncomputable section

open NumberField IsDedekindDomain ArithmeticFunction

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

variable {K : Type} [Field K] [NumberField K]

/-- **The residue field of `𝓞_{K_𝔭}` has `N𝔭` elements** (PROVED): it is `𝓞_K / 𝔭`. -/
theorem natCard_residueField_adicCompletionIntegers (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) = Ideal.absNorm 𝔭.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (𝔭.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv).symm

/-- **Northcott for the residue cardinality** (PROVED): finitely many primes of `K` have residue
field of at most `B` elements. -/
instance northcott_natCard_residueField_K :
    Northcott (fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) := by
  have h : (fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) =
      fun 𝔭 => Ideal.absNorm 𝔭.asIdeal := funext natCard_residueField_adicCompletionIntegers
  rw [h]
  infer_instance

/-- The quotient `𝓞_K / 𝔭` is finite (PROVED). -/
theorem finite_quotient (𝔭 : HeightOneSpectrum (𝓞 K)) : Finite (𝓞 K ⧸ 𝔭.asIdeal) := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h0
  exact Nat.finite_of_card_ne_zero h0

/-- `N𝔭` is a power of the residue characteristic `ℓ`, and `ℓ ∈ 𝔭` (PROVED). -/
theorem exists_prime_absNorm_eq_pow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ n : ℕ, ℓ.Prime ∧ 0 < n ∧ Ideal.absNorm 𝔭.asIdeal = ℓ ^ n ∧
      ((ℓ : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
  have := finite_quotient 𝔭
  have := 𝔭.isMaximal
  let _ : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  let _ : Fintype (𝓞 K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  obtain ⟨ℓ, hchar⟩ := CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)
  have hℓ : ℓ.Prime := CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) ℓ
  obtain ⟨n, -, hcard⟩ := FiniteField.card (𝓞 K ⧸ 𝔭.asIdeal) ℓ
  refine ⟨ℓ, n, hℓ, n.pos, ?_, ?_⟩
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast]
    exact_mod_cast CharP.cast_eq_zero (𝓞 K ⧸ 𝔭.asIdeal) ℓ

/-- The residue cardinality of `𝔭` is a prime power (PROVED). -/
theorem isPrimePow_natCard_residueField (𝔭 : HeightOneSpectrum (𝓞 K)) :
    IsPrimePow (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) := by
  obtain ⟨ℓ, n, hℓ, hn, hN, -⟩ := exists_prime_absNorm_eq_pow 𝔭
  rw [natCard_residueField_adicCompletionIntegers, hN]
  exact ⟨ℓ, n, hℓ.prime, hn, rfl⟩

/-- **Finitely many primes above `p`** (PROVED): they are among the prime factors of `p 𝓞_K`. -/
theorem primesAbove_finite (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p ≠ 0) :
    (primesAbove K p).Finite := by
  have hI : Ideal.span {((p : ℤ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors hI).subset fun 𝔭 h𝔭 => ?_
  show 𝔭.asIdeal ∣ Ideal.span {((p : ℤ) : 𝓞 K)}
  rw [Ideal.dvd_span_singleton]
  exact h𝔭

/-- The finite set of primes of `K` above `p ≠ 0`. -/
def primesAboveFinset (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (primesAbove_finite K hp).toFinset

/-- Membership in `primesAboveFinset` (PROVED). -/
theorem mem_primesAboveFinset {p : ℕ} (hp : p ≠ 0) {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ primesAboveFinset K p hp ↔ ((p : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
  rw [primesAboveFinset, Set.Finite.mem_toFinset]; rfl

section Vanish

variable {R : Type*} [CommSemiring R]

/-- If `f 1 = 1` and `f` vanishes at the divisors `≠ 1` of `n`, then `(f * g) n = g n` (PROVED). -/
theorem mul_apply_of_vanish' {f g : ArithmeticFunction R} {n : ℕ} (hf1 : f 1 = 1)
    (hf : ∀ m, m ∣ n → m ≠ 1 → f m = 0) : (f * g) n = g n := by
  rw [mul_apply, Finset.sum_eq_single (1, n)]
  · simp [hf1]
  · rintro ⟨a, b⟩ hab hne
    have h := Nat.mem_divisorsAntidiagonal.mp hab
    by_cases ha : a = 1
    · subst ha; simp only [one_mul] at h; exact absurd (by rw [h.1]) hne
    · rw [hf a ⟨b, h.1.symm⟩ ha, zero_mul]
  · intro h
    have hn : n = 0 := by
      by_contra hn; exact h (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩)
    simp [hn]

/-- A finite product of factors with value `1` at `1` vanishing at the divisors `≠ 1` of `n` has
the same property (PROVED). -/
theorem prod_vanish' {ι : Type*} (f : ι → ArithmeticFunction R) (n : ℕ) (s : Finset ι)
    (hf : ∀ i ∈ s, f i 1 = 1 ∧ ∀ m, m ∣ n → m ≠ 1 → f i m = 0) :
    (∏ i ∈ s, f i) 1 = 1 ∧ ∀ m, m ∣ n → m ≠ 1 → (∏ i ∈ s, f i) m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, fun m _ hm => by simp [one_apply_ne hm]⟩
  | insert a s ha ih =>
    have ih' := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    refine ⟨by rw [mul_apply_one, hfa.1, ih'.1, one_mul], fun m hm hm1 => ?_⟩
    rw [mul_apply_of_vanish' hfa.1 fun m' hm' hm'1 => hfa.2 m' (hm'.trans hm) hm'1]
    exact ih'.2 m hm hm1

/-- **A Dirichlet convolution at `p ^ k` only sees the values at `p ^ j`, `j ≤ k`** (PROVED). -/
theorem mul_apply_prime_pow_congr {f g f' g' : ArithmeticFunction R} {p k : ℕ} (hp : p.Prime)
    (hf : ∀ j ≤ k, f (p ^ j) = f' (p ^ j)) (hg : ∀ j ≤ k, g (p ^ j) = g' (p ^ j)) :
    (f * g) (p ^ k) = (f' * g') (p ^ k) := by
  rw [mul_apply, mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h := Nat.mem_divisorsAntidiagonal.mp hx
  obtain ⟨i, hi, hxi⟩ := (Nat.dvd_prime_pow hp).mp ⟨x.2, h.1.symm⟩
  obtain ⟨j, hj, hxj⟩ := (Nat.dvd_prime_pow hp).mp ⟨x.1, by rw [mul_comm]; exact h.1.symm⟩
  rw [hxi, hxj, hf i hi, hg j hj]

end Vanish

section Regroup

variable {R : Type*} [CommRing R]

/-- **An Euler product over the primes of `K` at `p ^ k`** (PROVED): only the primes `𝔭 ∣ p`
contribute; a prime not above `p` has `N𝔭` a power of another prime, so its factor vanishes at
every divisor `≠ 1` of `p ^ k`. -/
theorem eulerProduct_apply_prime_pow (f : HeightOneSpectrum (𝓞 K) → PowerSeries R)
    (hf : ∀ 𝔭, PowerSeries.constantCoeff (f 𝔭) = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    eulerProduct (fun 𝔭 => ofPowerSeries
        (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) (f 𝔭)) (p ^ k) =
      (∏ 𝔭 ∈ primesAboveFinset K p hp.ne_zero, ofPowerSeries
        (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) (f 𝔭)) (p ^ k) := by
  classical
  set q := fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
    Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) with hq_def
  set T := primesAboveFinset K p hp.ne_zero
  have hf1 : ∀ 𝔭, ofPowerSeries (q 𝔭) (f 𝔭) 1 = 1 := fun 𝔭 => by
    rw [ofPowerSeries_apply_one, hf]
  have hvan : ∀ 𝔭, 𝔭 ∉ T → ∀ m, m ∣ p ^ k → m ≠ 1 → ofPowerSeries (q 𝔭) (f 𝔭) m = 0 := by
    intro 𝔭 h𝔭 m hm hm1
    obtain ⟨ℓ, n, hℓ, hn, hN, hmem⟩ := exists_prime_absNorm_eq_pow 𝔭
    have hq : q 𝔭 = ℓ ^ n := by
      rw [hq_def]; dsimp only; rw [natCard_residueField_adicCompletionIntegers, hN]
    have hq1 : 1 < q 𝔭 := by rw [hq]; exact Nat.one_lt_pow hn.ne' hℓ.one_lt
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
    rw [ofPowerSeries_apply hq1, Function.extend_apply']
    · rfl
    rintro ⟨l, hl⟩
    rcases j with _ | j
    · exact hm1 (pow_zero _)
    rcases l with _ | l
    · exact (Nat.one_lt_pow (Nat.succ_ne_zero j) hp.one_lt).ne (by simpa using hl)
    · have hdvd : ℓ ∣ p ^ (j + 1) := by
        have : ℓ ∣ q 𝔭 ^ (l + 1) := by
          rw [hq]; exact (dvd_pow_self ℓ hn.ne').trans (dvd_pow_self _ (Nat.succ_ne_zero l))
        simpa [hl] using this
      have hℓp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hdvd)
      exact h𝔭 ((mem_primesAboveFinset hp.ne_zero).mpr (hℓp ▸ hmem))
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp
    (tendsTo_eulerProduct_ofPowerSeries q f hf (p ^ k))
  have key := hs0 (s0 ∪ T) Finset.subset_union_left
  rw [← key, ← Finset.prod_sdiff (Finset.subset_union_right (s₁ := s0) (s₂ := T)), mul_comm]
  have hrest := prod_vanish' (fun 𝔭 => ofPowerSeries (q 𝔭) (f 𝔭)) (p ^ k) ((s0 ∪ T) \ T)
    fun 𝔭 h𝔭 => ⟨hf1 𝔭, hvan 𝔭 (Finset.mem_sdiff.mp h𝔭).2⟩
  rw [mul_comm, mul_apply_of_vanish' hrest.1 hrest.2]

/-- **An Euler product over the primes of `K` is multiplicative** (PROVED): each factor
`f_𝔭(N𝔭^{-s})` is, `N𝔭` being a prime power. -/
theorem isMultiplicative_eulerProduct_ofPowerSeries (f : HeightOneSpectrum (𝓞 K) → PowerSeries R)
    (hf : ∀ 𝔭, PowerSeries.constantCoeff (f 𝔭) = 1) :
    IsMultiplicative (eulerProduct (fun 𝔭 => ofPowerSeries
        (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) (f 𝔭))) :=
  isMultiplicative_eulerProduct _ fun 𝔭 =>
    isMultiplicative_ofPowerSeries_of_isPrimePow _ (isPrimePow_natCard_residueField 𝔭) _ (hf 𝔭)

end Regroup

section Twisted

/-- The factor of CST's `twistedLFunction` at `𝔭`, as a power series in `T = N𝔭^{-s}`: Mathlib's
`localPowerSeries` of `E/K_𝔭` with `T` replaced by `χ(𝔭) T`. -/
def twistFactor (E : WeierstrassCurve ℚ) (χv : HeightOneSpectrum (𝓞 K) → ℂ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  PowerSeries.rescale (χv 𝔭) (PowerSeries.map (Int.castRingHom ℂ)
    (((E.baseChange K).baseChange (𝔭.adicCompletion K)).localPowerSeries
      (𝔭.adicCompletionIntegers K)))

/-- **CST's twisted `L`-function is the Euler product of the `twistFactor`s** (PROVED, by
definition). -/
theorem twistedLFunction_eq_eulerProduct (E : WeierstrassCurve ℚ)
    (χv : HeightOneSpectrum (𝓞 K) → ℂ) :
    twistedLFunction E χv = eulerProduct (fun 𝔭 => ofPowerSeries
      (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) (twistFactor E χv 𝔭)) :=
  rfl

/-- **The factors of the twisted `L`-function have constant coefficient `1`** (PROVED). -/
theorem constantCoeff_twistFactor (E : WeierstrassCurve ℚ) (χv : HeightOneSpectrum (𝓞 K) → ℂ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) : PowerSeries.constantCoeff (twistFactor E χv 𝔭) = 1 := by
  rw [twistFactor, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    pow_zero, one_mul, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    WeierstrassCurve.localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  simp

end Twisted

end ZInQ.Contrib.CloudB3RC53.GenusOdd
