import ZInQKernel.Contrib.HilbertDifferent.Transport

/-!
# Prime localization preserves every integral congruence

These are the actual localization map and maximal ideal, not completion maps.
Mathlib v4.35 supplies both the contraction of every maximal-ideal power and
`equivQuotMaximalIdealPow`; the latter proves surjectivity modulo every power.
The statements include exponent zero. An automorphism of a local ring preserves
its unique maximal ideal and its powers. These supply the three concrete
hypotheses of the already proved power-inertia transport theorem.

Source interfaces: Mathlib/RingTheory/Localization/AtPrime/Basic.lean and
Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean, at the unchanged v4.35 pin.
No finite-module claim for a split-prime base localization is introduced.
-/

namespace ZInQ.Contrib.HilbertDifferent

section PrimeLocalization

variable {R : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal]

/-- Contracting the actual localized maximal-ideal power gives the original prime power,
including the zeroth power. -/
theorem primeLocalization_comap_maximalIdeal_pow (n : ℕ) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n).comap
      (algebraMap R (Localization.AtPrime P)) = P ^ n :=
  IsLocalization.AtPrime.under_maximalIdeal_pow P (Localization.AtPrime P) n

/-- The original ring maps onto every quotient of its prime localization by a maximal-ideal
power. This is an algebraic localization assertion, not completeness or topological density. -/
theorem primeLocalization_surjective_mod_pow (n : ℕ) (y : Localization.AtPrime P) :
    ∃ x : R, y - algebraMap R (Localization.AtPrime P) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n := by
  let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow P (Localization.AtPrime P) n
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (e.symm (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n) y))
  refine ⟨x, ?_⟩
  have he : e (Ideal.Quotient.mk (P ^ n) x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n) y := by
    rw [hx, e.apply_symm_apply]
  rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk] at he
  exact Ideal.Quotient.eq.mp he.symm

end PrimeLocalization

/-- Every algebra automorphism of a local ring preserves each maximal-ideal power. -/
theorem algAut_mem_maximalIdeal_pow {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] (σ : B ≃ₐ[A] B) (n : ℕ) {y : B}
    (hy : y ∈ IsLocalRing.maximalIdeal B ^ n) :
    σ • y ∈ IsLocalRing.maximalIdeal B ^ n := by
  have hmax : (IsLocalRing.maximalIdeal B).map σ.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal B := IsLocalRing.map_ringEquiv_maximalIdeal σ.toRingEquiv
  have hm : (IsLocalRing.maximalIdeal B ^ n).map σ.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal B ^ n := by
    rw [Ideal.map_pow, hmax]
  have h := Ideal.mem_map_of_mem σ.toRingEquiv.toRingHom hy
  rw [hm] at h
  exact h

end ZInQ.Contrib.HilbertDifferent
