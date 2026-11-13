import Mathlib

/-!
# t-brauer-purity: the unit-radicand Kummer step of Abhyankar's lemma is unramified

Step (b) of the proof of leaf T2 (`PkgI2.AbhyankarDVR`, docs/research/t-brauer-purity.md §2, §4):
adjoining an `e`-th root `w` of an element `u` of a Dedekind domain `A`, with `e` invertible, gives
an extension unramified at every prime `P` of the integral closure `B` with `u ∉ P`.

Proof: if `P` were ramified it would divide the different ideal (`dvd_differentIdeal_iff`), which
contains `g'(w)` for `g` the minimal polynomial of `w` (`aeval_derivative_mem_differentIdeal`).
`g ∣ Xᵉ - u` gives `e wᵉ⁻¹ = g'(w) h(w) ∈ P`, hence `wᵉ = u ∈ P`.
-/

open Polynomial

namespace TBrauerPurity

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem isUnramifiedAt_of_pow_eq (A K L B : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L] [Module.IsTorsionFree A B] [Module.Finite A B]
    (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : A)) (w : B) (u : A)
    (hw : w ^ e = algebraMap A B u) (hgen : Algebra.adjoin K {algebraMap B L w} = ⊤)
    (P : Ideal B) [P.IsPrime] (hu : algebraMap A B u ∉ P) : Algebra.IsUnramifiedAt A P := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv B L).symm _
  by_contra hP
  rw [← dvd_differentIdeal_iff] at hP
  have hle : differentIdeal A B ≤ P := Ideal.le_of_dvd hP
  have hmem := hle (aeval_derivative_mem_differentIdeal A K L w hgen)
  have hint : IsIntegral A w := IsIntegralClosure.isIntegral A L w
  have haev : aeval w (X ^ e - C u) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hw, sub_self]
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint haev
  have hder : aeval w (derivative (X ^ e - C u)) =
      aeval w (derivative (minpoly A w)) * aeval w h := by
    rw [hh, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  have hin : aeval w (derivative (X ^ e - C u : A[X])) ∈ P := by
    rw [hder]; exact P.mul_mem_right _ hmem
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, aeval_C, map_pow,
    aeval_X] at hin
  have heB : IsUnit (algebraMap A B (e : A)) := he.map _
  have hpow : w ^ (e - 1) ∈ P := by
    rcases (Ideal.IsPrime.mem_or_mem ‹_› hin) with h1 | h1
    · rw [map_natCast] at h1 heB
      exact absurd (P.eq_top_of_isUnit_mem h1 heB) (Ideal.IsPrime.ne_top ‹_›)
    · exact h1
  apply hu
  rw [← hw, show e = (e - 1) + 1 by omega, pow_succ]
  exact P.mul_mem_right _ hpow

/-- Corollary: ramification index one at such `P`. -/
theorem ramificationIdx_eq_one_of_pow_eq (A K L B : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L] [Module.IsTorsionFree A B] [Module.Finite A B]
    (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : A)) (w : B) (u : A)
    (hw : w ^ e = algebraMap A B u) (hgen : Algebra.adjoin K {algebraMap B L w} = ⊤)
    (P : Ideal B) [P.IsPrime] (hu : algebraMap A B u ∉ P) : P.ramificationIdx A = 1 := by
  have := isUnramifiedAt_of_pow_eq A K L B e he0 he w u hw hgen P hu
  exact Ideal.ramificationIdx_eq_one P A

end TBrauerPurity

#print axioms TBrauerPurity.isUnramifiedAt_of_pow_eq
#print axioms TBrauerPurity.ramificationIdx_eq_one_of_pow_eq
