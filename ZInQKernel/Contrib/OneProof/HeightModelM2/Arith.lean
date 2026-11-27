import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Two facts on Dedekind domains, for the global sections of `ε*Ω^g`

* `exists_mul_eq_of_not_le`: for a nonzero prime `Q` not inside the prime `P` and `a ≠ 0`, some
  `d ∉ P` lies in `a R_Q` (`t * d = a * y` with `t ∉ Q`); the proof uses that `R_Q` is a discrete
  valuation ring.
* `finite_setOf_mem`: a nonzero element lies in finitely many primes (Mathlib's
  `Ideal.finite_factors`). -/
/-! Arithmetic of a Dedekind domain used for the lattice of global sections. -/
set_option linter.style.haveILetI false
namespace ZInQ.HeightModelM2

/-- **Clearing denominators away from `P`.** In a Dedekind domain, for a nonzero prime `Q` not
contained in the prime `P` and a nonzero `a`, some `d ∉ P` is a multiple of `a` in `R_Q`:
`t * d = a * y` with `t ∉ Q`. -/
theorem exists_mul_eq_of_not_le {R : Type*} [CommRing R] [IsDedekindDomain R] (P Q : Ideal R)
    [P.IsPrime] [hQp : Q.IsPrime] (hQ : Q ≠ ⊥) (hPQ : ¬ Q ≤ P) {a : R} (ha : a ≠ 0) :
    ∃ d ∉ P, ∃ t ∉ Q, ∃ y : R, t * d = a * y := by
  obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hPQ
  let Rq := Localization.AtPrime Q
  haveI : IsDiscreteValuationRing Rq :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hQ Rq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rq
  have hinj : Function.Injective (algebraMap R Rq) :=
    IsLocalization.injective Rq (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hspan : Ideal.span {algebraMap R Rq a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact fun h => ha (hinj (by rw [h, map_zero]))
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hspan hϖ
  have hxm : algebraMap R Rq x ∈ IsLocalRing.maximalIdeal Rq := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hxQ
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hxm
  obtain ⟨z, hz⟩ := hxm
  have hmem : algebraMap R Rq (x ^ n) ∈ Ideal.map (algebraMap R Rq) (Ideal.span {a}) := by
    rw [Ideal.map_span, Set.image_singleton, hn, Ideal.mem_span_singleton']
    exact ⟨z ^ n, by rw [map_pow, ← hz, mul_pow]⟩
  obtain ⟨⟨⟨w, hw⟩, ⟨t, ht⟩⟩, h⟩ :=
    (IsLocalization.mem_map_algebraMap_iff Q.primeCompl Rq).mp hmem
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  -- `x^n * t = y * a` in `R_Q`, hence after a further `c ∉ Q` in `R`
  rw [← map_mul] at h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists Q.primeCompl Rq).mp h
  refine ⟨x ^ n, fun h' => hxP (‹P.IsPrime›.mem_of_pow_mem n h'), c * t,
    fun h' => ?_, c * y, ?_⟩
  · rcases hQp.mem_or_mem h' with h'' | h''
    · exact c.2 h''
    · exact ht h''
  · calc c * t * x ^ n = c * (x ^ n * t) := by ring
      _ = c * (y * a) := hc
      _ = a * (c * y) := by ring

/-- In a Dedekind domain, the primes containing a nonzero element form a finite set. -/
theorem finite_setOf_mem {R : Type*} [CommRing R] [IsDedekindDomain R] {f : R} (hf : f ≠ 0) :
    {p : PrimeSpectrum R | f ∈ p.asIdeal}.Finite := by
  have hI : Ideal.span {f} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hf
  have hfin := Ideal.finite_factors hI
  let φ : {p : PrimeSpectrum R | f ∈ p.asIdeal} →
      {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {f}} := fun p =>
    ⟨⟨p.1.asIdeal, p.1.isPrime, fun h => hf (by rw [← Ideal.mem_bot, ← h]; exact p.2)⟩,
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr p.2)⟩
  have hφ : Function.Injective φ := by
    intro p q h
    apply Subtype.ext
    apply PrimeSpectrum.ext
    exact congrArg (fun v => v.1.asIdeal) h
  haveI : Finite {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {f}} :=
    hfin.to_subtype
  haveI := Finite.of_injective φ hφ
  exact Set.toFinite _

end ZInQ.HeightModelM2
