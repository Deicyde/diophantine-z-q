import Mathlib

set_option linter.style.haveILetI false

open Order

universe u

namespace CurveInfra

/-- Copied verbatim from g0-dim (`scratch/g0-dim/part_dim.lean`). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- Noether normalization data for a domain of finite type: `dim R = s = trdeg_K R`. -/
theorem exists_dim_eq_trdeg (K : Type u) [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] :
    ∃ s : ℕ, ringKrullDim R = s ∧ Algebra.trdeg K R = s := by
  obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) R :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ginj
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]
  · rw [← trdeg_add_eq K (MvPolynomial (Fin s) K) (A := R), MvPolynomial.trdeg_of_isDomain,
      trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := R)]
    simp

/-- Transcendence degree is unchanged by passing to a localization (e.g. the fraction field). -/
theorem trdeg_eq_of_isLocalization (K : Type*) [Field K] (R : Type u) [CommRing R] [IsDomain R]
    [Algebra K R] (F : Type u) [Field F] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [IsFractionRing R F] : Algebra.trdeg K F = Algebra.trdeg K R := by
  haveI : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  haveI : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsFractionRing.injective R F)
  rw [← trdeg_add_eq K R (A := F), trdeg_eq_zero (R := R) (A := F), add_zero]

end CurveInfra
