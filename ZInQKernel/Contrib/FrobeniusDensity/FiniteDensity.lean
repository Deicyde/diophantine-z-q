import ZInQKernel.Contrib.FrobeniusDensity.Tau_NumberTheory_Chebotarev_PrimeCounting_FrobeniusPrimeCount
import ZInQKernel.Contrib.FrobeniusDensity.Tau_NumberTheory_NumberField_Ideal_IntegersRat
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.C10.C10

/-!
# Finite Chebotarev with arbitrary finite-set avoidance

The density input in this file is an actual ported proof, not a `Fact` or an
unproved Chebotarev premise. Nonzero natural density makes the prime-ideal set
infinite; Northcott finiteness of bounded norms makes its norms unbounded.
Over `ℚ`, these norms are the actual rational primes. The specified Galois
element is realized at a prime above that rational prime, not merely counted
up to conjugacy.
-/

noncomputable section

namespace ZInQ.Contrib.FrobeniusDensity

open NumberField IsDedekindDomain Filter TauCeti
open scoped NumberField Topology

/-- The proved natural-density input for the specified finite Galois class. -/
theorem finite_frobenius_hasNaturalDensity (M : Type*) [Field M] [NumberField M]
    [IsGalois ℚ M] (σ : M ≃ₐ[ℚ] M) :
    NumberField.Set.HasNaturalDensity
      (NumberField.Chebotarev.frobeniusPrimeSet ℚ M (ConjClasses.mk σ))
      ((Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card (M ≃ₐ[ℚ] M)) :=
  NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet ℚ M (ConjClasses.mk σ)

/-- The finite Frobenius class has strictly positive density, not merely a
nominally assigned density value. -/
theorem finite_frobenius_density_pos (M : Type*) [Field M] [NumberField M]
    [IsGalois ℚ M] (σ : M ≃ₐ[ℚ] M) :
    0 < (Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card (M ≃ₐ[ℚ] M) := by
  have hne : (Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card (M ≃ₐ[ℚ] M) ≠ 0 :=
    (ConjClasses.mk σ).card_carrier_div_card_ne_zero
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact lt_of_le_of_ne (finite_frobenius_hasNaturalDensity M σ).nonneg hne.symm

/-- Positive finite-quotient density yields infinitely many actual
base prime ideals. -/
theorem finite_frobenius_primes_infinite (M : Type*) [Field M] [NumberField M]
    [IsGalois ℚ M] (σ : M ≃ₐ[ℚ] M) :
    (NumberField.Chebotarev.frobeniusPrimeSet ℚ M (ConjClasses.mk σ)).Infinite := by
  apply (finite_frobenius_hasNaturalDensity M σ).infinite
  exact (finite_frobenius_density_pos M σ).ne'

/-- Infinitely many prime ideals in a number field have arbitrarily large
absolute norm. No prime ideal theorem is used in this elementary implication. -/
theorem exists_absNorm_gt_of_infinite {K : Type*} [Field K] [NumberField K]
    {A : Set (HeightOneSpectrum (𝓞 K))} (hA : A.Infinite) (B : ℕ) :
    ∃ 𝔭 ∈ A, B < Ideal.absNorm 𝔭.asIdeal := by
  have hfinite : {𝔭 : HeightOneSpectrum (𝓞 K) | Ideal.absNorm 𝔭.asIdeal ≤ B}.Finite :=
    Northcott.finite_le B
  obtain ⟨𝔭, h𝔭, hnot⟩ := hA.exists_notMem_finite hfinite
  exact ⟨𝔭, h𝔭, lt_of_not_ge hnot⟩

/-- The exact finite existence statement, avoiding every member of the
provided finite set of natural numbers. -/
theorem exists_finite_arithFrob_avoiding (M : Type*) [Field M] [NumberField M]
    [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧
        IsArithFrobAt ℤ σ Q := by
  obtain ⟨𝔭, h𝔭, hlarge⟩ :=
    exists_absNorm_gt_of_infinite (finite_frobenius_primes_infinite M σ) (S.sup id)
  let p := Ideal.absNorm 𝔭.asIdeal
  have hp : p.Prime := by
    change (Ideal.absNorm 𝔭.asIdeal).Prime
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have hpS : p ∉ S := by
    intro h
    exact (not_le_of_gt hlarge) (Finset.le_sup (f := id) h)
  obtain ⟨Q, hσ⟩ :=
    NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
  have : Q.1.IsPrime := Q.2.1
  have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 ℚ)) = 𝔭.asIdeal := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact Rat.RingOfIntegers.ideal_span_absNorm_eq_self 𝔭.asIdeal
  have hbase : 𝔭.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hmap, Ideal.under, Ideal.comap_map_of_bijective _
      Rat.algebraMap_int_ringOfIntegers_bijective]
  have hQp : Q.1.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← Ideal.under_under (B := 𝓞 ℚ), ← Q.2.2.over, hbase]
  have hQuRat : Algebra.IsUnramifiedAt (𝓞 ℚ) Q.1 :=
    NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q.1
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ))
      Rat.algebraMap_int_ringOfIntegers_bijective.surjective
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q.1 := hQuRat
  have hQuInt : Algebra.IsUnramifiedAt ℤ Q.1 :=
    Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization Q.1.primeCompl)
  exact ⟨p, hp, hpS, Q.1, Q.2.1, hQp, hQuInt,
    (Ideal.isArithFrobAt_ringOfIntegers_rat_iff σ Q.1).mp hσ⟩

/-- The baseline finite Chebotarev proposition is discharged by the actual
density proof and the proved finite-set avoidance argument above. -/
theorem chebotarevExists : PkgI6.ChebotarevExists := by
  intro M _ _ _ S σ
  exact exists_finite_arithFrob_avoiding M S σ

/-- The identical finite interface used by the existing C10 glue. -/
theorem chebotarevExists_C10 : GlueC10.ChebotarevExists :=
  chebotarevExists

end ZInQ.Contrib.FrobeniusDensity
