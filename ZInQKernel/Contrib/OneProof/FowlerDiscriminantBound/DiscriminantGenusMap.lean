import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.RamifiedGenusMap
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.RamifiedPrimes
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Discriminant primes in the ramified ideal class map

In degree two, a rational discriminant prime has one prime above it, of
ramification index two. This uses the discriminant criterion and `∑ eᵢ fᵢ = 2`,
with no restriction on the rational prime.
-/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField IsDedekindDomain Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

private theorem exists_primeOver_of_dvd_discr (hK : Module.finrank ℚ K = 2)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ (discr K).natAbs) :
    ∃ P : Ideal (𝓞 K),
      P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ∧ P.ramificationIdx ℤ = 2 ∧
      ∀ Q ∈ (span {(p : ℤ)}).primesOver (𝓞 K), Q = P := by
  classical
  let q : Ideal ℤ := span {(p : ℤ)}
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hq : q ≠ ⊥ := span_singleton_eq_bot.not.mpr hpz.ne_zero
  let : q.IsMaximal := ((span_singleton_prime hpz.ne_zero).mpr hpz).isMaximal hq
  have hram : ¬ Algebra.IsUnramifiedIn (𝓞 K) q :=
    (mem_ramifiedPrimes_iff.mp ((mem_ramifiedPrimes_iff_dvd_discr hp).mpr
      (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)))).2
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one] at hram
  push Not at hram
  obtain ⟨P, hP, hlo, he⟩ := hram
  let S := q.primesOver (𝓞 K)
  let : Fintype S := inferInstanceAs (Fintype (q.primesOver (𝓞 K)))
  let x : S := ⟨P, hP, hlo⟩
  let ef (y : S) := y.1.ramificationIdx ℤ * y.1.inertiaDeg ℤ
  have hepos (y : S) : 0 < y.1.ramificationIdx ℤ := by
    let := y.2.1
    let := y.2.2
    exact ramificationIdx_pos_of_isDedekindDomain' y.1 hq
  have hfpos (y : S) : 0 < y.1.inertiaDeg ℤ := by
    let := y.2.1
    exact inertiaDeg_pos y.1 ℤ
  have hPlow : 2 ≤ P.ramificationIdx ℤ := by
    have hh : 0 < P.ramificationIdx ℤ := hepos x
    omega
  have hPle : P.ramificationIdx ℤ ≤ ef x := Nat.le_mul_of_pos_right _ (hfpos x)
  have hx : 2 ≤ ef x := hPlow.trans hPle
  have hsum : ∑ y : S, ef y = 2 := by
    rw [Ideal.sum_ramification_inertia_eq_finrank q (𝓞 K), RingOfIntegers.rank, hK]
  have huniq (y : S) : y = x := by
    by_contra hne
    have hy : y ∈ (Finset.univ : Finset S).erase x := by simpa using hne
    have hpos : 0 < ef y := Nat.mul_pos (hepos y) (hfpos y)
    have hle := Finset.single_le_sum (f := ef) (fun _ _ => Nat.zero_le _) hy
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at hsum
    omega
  have hxle : ef x ≤ 2 := hsum ▸ Finset.single_le_sum (f := ef)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  refine ⟨P, ⟨hP, hlo⟩, le_antisymm (hPle.trans hxle) hPlow, ?_⟩
  intro Q hQ
  exact congrArg Subtype.val (huniq (⟨Q, hQ⟩ : S))

private theorem genusPrimeExists (hK : Module.finrank ℚ K = 2)
    (p : (discr K).natAbs.primeFactors) :
    ∃ P : Ideal (𝓞 K),
      P ∈ (span {(p.1 : ℤ)}).primesOver (𝓞 K) ∧ P.ramificationIdx ℤ = 2 ∧
      ∀ Q ∈ (span {(p.1 : ℤ)}).primesOver (𝓞 K), Q = P :=
  exists_primeOver_of_dvd_discr hK (Nat.prime_of_mem_primeFactors p.2)
    (Nat.dvd_of_mem_primeFactors p.2)

/-- The prime ideal above a rational prime dividing the field discriminant. -/
noncomputable def genusRamifiedPrime (hK : Module.finrank ℚ K = 2)
    (p : (discr K).natAbs.primeFactors) : HeightOneSpectrum (𝓞 K) := by
  classical
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hP := (genusPrimeExists hK p).choose_spec.1
  have hq : (span {(p.1 : ℤ)} : Ideal ℤ) ≠ ⊥ := by simpa using hp.ne_zero
  exact ⟨(genusPrimeExists hK p).choose, hP.1, Ideal.ne_bot_of_mem_primesOver hq hP⟩

theorem genusRamifiedPrime_liesOver (hK : Module.finrank ℚ K = 2)
    (p : (discr K).natAbs.primeFactors) :
    (genusRamifiedPrime hK p).asIdeal.LiesOver (span {(p.1 : ℤ)}) :=
  (genusPrimeExists hK p).choose_spec.1.2

/-- The same prime upstairs cannot lie over two different positive rational primes. -/
theorem genusRamifiedPrime_injective (hK : Module.finrank ℚ K = 2) :
    Function.Injective (genusRamifiedPrime hK) := by
  intro p q heq
  have hP := (genusRamifiedPrime_liesOver hK p).1
  have hQ := (genusRamifiedPrime_liesOver hK q).1
  rw [heq] at hP
  apply Subtype.ext
  have h := Ideal.span_singleton_eq_span_singleton.mp (hP.trans hQ.symm)
  simpa using Int.natAbs_eq_iff_associated.mpr h

theorem genusRamifiedPrime_sq (hK : Module.finrank ℚ K = 2)
    (p : (discr K).natAbs.primeFactors) :
    (genusRamifiedPrime hK p).asIdeal ^ 2 = Ideal.span {(p.1 : 𝓞 K)} := by
  classical
  let q : Ideal ℤ := span {(p.1 : ℤ)}
  let P := (genusRamifiedPrime hK p).asIdeal
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hpz : Prime (p.1 : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hq : q ≠ ⊥ := span_singleton_eq_bot.not.mpr hpz.ne_zero
  let : q.IsMaximal := ((span_singleton_prime hpz.ne_zero).mpr hpz).isMaximal hq
  let : P.LiesOver q := genusRamifiedPrime_liesOver hK p
  have hP : P ∈ q.primesOver (𝓞 K) := (genusPrimeExists hK p).choose_spec.1
  have he : P.ramificationIdx ℤ = 2 := (genusPrimeExists hK p).choose_spec.2.1
  let Q := q.map (algebraMap ℤ (𝓞 K))
  have hQ : Q ≠ ⊥ := map_ne_bot_of_ne_bot hq
  have hfactor : (factors Q).toFinset = {P} := by
    change IsDedekindDomain.primesOverFinset q (𝓞 K) = {P}
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(IsDedekindDomain.mem_primesOverFinset_iff hq (𝓞 K)).2 hP, fun y hy => ?_⟩
    exact (genusPrimeExists hK p).choose_spec.2.2 y
      ((IsDedekindDomain.mem_primesOverFinset_iff hq (𝓞 K)).1 hy)
  have hcount := IsDedekindDomain.ramificationIdx_eq_factors_count q P hQ
  have hprod : P ^ (factors Q).count P = Q := by
    have h := Finset.prod_multiset_map_count (factors Q) id
    rw [hfactor, Finset.prod_singleton, Multiset.map_id] at h
    exact h.symm.trans (associated_iff_eq.mp (factors_prod hQ))
  change P ^ 2 = Ideal.span {(p.1 : 𝓞 K)}
  rw [← he, hcount, hprod]
  change Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p.1 : ℤ)}) = _
  simp [Ideal.map_span]

/-- The class-group map on subsets of the actual distinct rational discriminant primes. -/
noncomputable def discriminantGenusClassMap (hK : Module.finrank ℚ K = 2) :
    Multiplicative ((discr K).natAbs.primeFactors → ZMod 2) →* ClassGroup (𝓞 K) :=
  genusClassMap (genusRamifiedPrime hK) Subtype.val (genusRamifiedPrime_sq hK)

section PrimeProducts

variable {ι : Type*} [Fintype ι] {p : ι → ℕ}

private theorem genusInteger_ne_zero (hp : ∀ i, (p i).Prime) (a : ι → ZMod 2) :
    genusInteger p a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp i).ne_zero

private theorem genusInteger_factorization (hp : ∀ i, (p i).Prime) (a : ι → ZMod 2) (q : ℕ) :
    (genusInteger p a).factorization q =
      ∑ i, (Finsupp.single (p i) (a i).val : ℕ →₀ ℕ) q := by
  unfold genusInteger
  rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero), Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun f : ℕ →₀ ℕ => f q) ((hp i).factorization_pow (k := (a i).val))

private theorem genusInteger_factorization_at (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (a : ι → ZMod 2) (i : ι) :
    (genusInteger p a).factorization (p i) = (a i).val := by
  classical
  rw [genusInteger_factorization hp]
  rw [Finset.sum_eq_single i]
  · exact Finsupp.single_eq_same
  · intro j _ hji
    exact Finsupp.single_eq_of_ne (fun hij => hji (hinj hij.symm))
  · simp

/-- Distinct subsets give distinct rational products. -/
theorem genusInteger_injective (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (genusInteger p) := by
  intro a b hab
  funext i
  apply ZMod.val_injective 2
  rw [← genusInteger_factorization_at hp hinj a i, ← genusInteger_factorization_at hp hinj b i,
    hab]

/-- The rational product of a subset of distinct primes is squarefree. -/
theorem genusInteger_squarefree (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (a : ι → ZMod 2) : Squarefree (genusInteger p a) := by
  classical
  apply Nat.squarefree_of_factorization_le_one (genusInteger_ne_zero hp a)
  intro q
  by_cases hq : ∃ i, p i = q
  · obtain ⟨i, rfl⟩ := hq
    rw [genusInteger_factorization_at hp hinj]
    exact Nat.le_of_lt_succ (a i).val_lt
  · rw [genusInteger_factorization hp, Finset.sum_eq_zero]
    · omega
    · intro i _
      exact Finsupp.single_eq_of_ne (fun h => hq ⟨i, h.symm⟩)

end PrimeProducts

/-- Every class in the image of the discriminant-prime subset map has square one. -/
theorem discriminantGenusClassMap_sq (hK : Module.finrank ℚ K = 2)
    (a : Multiplicative ((discr K).natAbs.primeFactors → ZMod 2)) :
    discriminantGenusClassMap hK a ^ 2 = 1 :=
  genusClassMap_sq (genusRamifiedPrime hK) Subtype.val (genusRamifiedPrime_sq hK) a

/-- A kernel element of the discriminant-prime subset map gives a generator of the
actual product ideal and a unit times the selected positive rational product. -/
theorem discriminantGenusClassMap_ker_generator (hK : Module.finrank ℚ K = 2)
    (a : (discriminantGenusClassMap hK).ker) :
    ∃ (α : 𝓞 K) (u : (𝓞 K)ˣ),
      (genusIdeal (genusRamifiedPrime hK) a.1.toAdd : Ideal (𝓞 K)) = Ideal.span {α} ∧
      α ^ 2 = (genusInteger Subtype.val a.1.toAdd : 𝓞 K) * u :=
  genusClassMap_ker_generator (genusRamifiedPrime hK) Subtype.val (genusRamifiedPrime_sq hK) a

end HDec.CMBranch.FowlerArithmetic
