import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-! Development file for ts-sn: the abstract criterion (Part 1). -/

open GlueDescent.B2Q NumberField

noncomputable section

namespace TSSN

theorem atPrime_congr' {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (h : p = q) [IsLocalization.AtPrime S p] :
    IsLocalization.AtPrime S q := by
  subst h
  assumption

/-- **Unramified at `p` from a normal-at-`p` subring** (PROVED). Let `L ⊂ ℚ̄` be a number field
and `A ⊆ L` a Noetherian subring with fraction field `L` in which the integers prime to `p` are
units, whose elements become integral over `ℤ` after multiplication by an integer prime to `p`,
whose maximal ideals contain `p`, and whose local rings at the primes over `p` have maximal ideal
`(p)`. Then `L` is unramified at `p`. (Proof: each `A_q` is a DVR, so `A` is integrally closed,
so `𝓞_L ⊆ A` and `A` is the localization of `𝓞_L` at the integers prime to `p`; hence
`(𝓞_L)_Q ≅ A_{QA}` has maximal ideal `(p)`, i.e. `e(Q/p) = 1`.) -/
theorem unramifiedAt_of_subring (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] (p : ℕ) [hp : Fact p.Prime] (A : Subring L)
    (hfrac : ∀ x : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a)
    [IsNoetherianRing A]
    (hpq : ∀ q : Ideal A, q.IsMaximal → (p : A) ∈ q)
    (hmax : ∀ (q : Ideal A) [q.IsPrime], (p : A) ∈ q →
      IsLocalRing.maximalIdeal (Localization.AtPrime q) =
        Ideal.span {(p : Localization.AtPrime q)})
    (hunit : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → IsUnit (n : A))
    (hint : ∀ y ∈ A, ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ IsIntegral ℤ ((n : L) * y)) :
    UnramifiedAt L p := by
  have hp0 : (p : A) ≠ 0 := by
    intro h
    have : ((p : A) : L) = 0 := by rw [h]; rfl
    simp only [Subring.coe_natCast, Nat.cast_eq_zero] at this
    exact hp.out.ne_zero this
  -- `L` is the fraction field of `A`
  haveI hFR : IsFractionRing A L := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      rw [isUnit_iff_ne_zero]
      intro h0
      exact nonZeroDivisors.coe_ne_zero ⟨y, hy⟩ (Subtype.ext h0)
    · intro x
      obtain ⟨a, ha, b, hb, hb0, h⟩ := hfrac x
      refine ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, mem_nonZeroDivisors_of_ne_zero ?_⟩⟩, h⟩
      intro h0
      exact hb0 (congrArg Subtype.val h0)
    · intro x y h
      exact ⟨1, by rw [Subtype.ext h]⟩
  -- the local rings at maximal ideals are DVRs
  have hloc : ∀ q : Ideal A, q ≠ ⊥ → [q.IsMaximal] →
      IsIntegrallyClosed (Localization.AtPrime q) := by
    intro q _ hqm
    have hm := hmax q (hpq q hqm)
    have hp0' : (p : Localization.AtPrime q) ≠ 0 := by
      rw [← map_natCast (algebraMap A (Localization.AtPrime q))]
      intro h
      exact hp0 (IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
        (h.trans (map_zero _).symm))
    have hnf : ¬ IsField (Localization.AtPrime q) := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
      exact hp0'
    haveI : IsDiscreteValuationRing (Localization.AtPrime q) :=
      ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr
        (show (IsLocalRing.maximalIdeal _).IsPrincipal from ⟨⟨_, hm⟩⟩)
    infer_instance
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_localization_maximal hloc
  -- `𝓞_L ⊆ A`
  have hO : ∀ x : 𝓞 L, (x : L) ∈ A := by
    intro x
    have hx : IsIntegral A (x : L) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A :=
    { toFun := fun x => ⟨x, hO x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra (𝓞 L) A := f.toAlgebra
  set M : Submonoid (𝓞 L) :=
    Algebra.algebraMapSubmonoid (𝓞 L) (Ideal.span {(p : ℤ)}).primeCompl with hM
  have hmemC : ∀ n : ℤ, n ∈ (Ideal.span {(p : ℤ)}).primeCompl ↔ ¬ (p : ℤ) ∣ n := fun n => by
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
  have hmemM : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → algebraMap ℤ (𝓞 L) n ∈ M := by
    intro n hn
    exact ⟨n, (hmemC n).mpr hn, rfl⟩
  haveI hLoc : IsLocalization M A := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, hn, rfl⟩
      have hn' : ¬ (p : ℤ) ∣ n := (hmemC n).mp hn
      simpa using hunit n hn'
    · intro y
      obtain ⟨n, hn, hni⟩ := hint y.1 y.2
      refine ⟨⟨⟨(n : L) * y.1, hni⟩, ⟨_, hmemM n hn⟩⟩, ?_⟩
      apply Subtype.ext
      change (y : L) * ((algebraMap (𝓞 L) A (algebraMap ℤ (𝓞 L) n) : A) : L) = (n : L) * y
      rw [algebraMap_int_eq, eq_intCast, map_intCast, mul_comm]
      rfl
    · intro x y h
      refine ⟨1, ?_⟩
      have h' : ((algebraMap (𝓞 L) A x : A) : L) = (algebraMap (𝓞 L) A y : A) :=
        congrArg Subtype.val h
      change (x : L) = y at h'
      rw [RingOfIntegers.ext h']
  -- the primes over `p`
  intro Q hQ hpQ
  have hdisj : Disjoint (M : Set (𝓞 L)) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnQ
    have hn' : ¬ (p : ℤ) ∣ n := (hmemC n).mp hn
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    obtain ⟨α, β, h⟩ := (Prime.coprime_iff_not_dvd hpr).mpr hn'
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    have : algebraMap ℤ (𝓞 L) (α * p + β * n) ∈ Q := by
      rw [map_add, map_mul, map_mul]
      exact Q.add_mem (Q.mul_mem_left _ (by simpa using hpQ)) (Q.mul_mem_left _ hnQ)
    rwa [h, map_one] at this
  set q : Ideal A := Q.map (algebraMap (𝓞 L) A) with hqdef
  haveI hq : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M A Q hQ hdisj
  have hqQ : q.comap (algebraMap (𝓞 L) A) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M A hQ hdisj
  have hpq' : (p : A) ∈ q := by
    have : algebraMap (𝓞 L) A ((p : ℤ) : 𝓞 L) ∈ q := Ideal.mem_map_of_mem _ hpQ
    simpa using this
  haveI h1 : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap (𝓞 L) A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) Q := atPrime_congr' hqQ
  let e : Localization.AtPrime Q ≃ₐ[𝓞 L] Localization.AtPrime q :=
    IsLocalization.algEquiv Q.primeCompl _ _
  have hunder : Q.under ℤ = Ideal.span {(p : ℤ)} := by
    have hmx : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible
        (Prime.irreducible (Nat.prime_iff_prime_int.mp hp.out))
    refine (hmx.eq_of_le ?_ ?_).symm
    · exact (Ideal.IsPrime.under ℤ Q).ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hpQ
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, hunder,
    Ideal.map_span, Set.image_singleton, map_natCast]
  have hT : (Ideal.span {(p : Localization.AtPrime q)}).IsMaximal := by
    rw [← hmax q hpq']
    exact IsLocalRing.maximalIdeal.isMaximal _
  have := Ideal.map_isMaximal_of_equiv e.symm (p := Ideal.span {(p : Localization.AtPrime q)})
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this

end TSSN
#print axioms TSSN.unramifiedAt_of_subring
