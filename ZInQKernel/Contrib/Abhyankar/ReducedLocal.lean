/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The Tau Ceti contributors

Modified for this contribution: minimal Mathlib v4.35.0 port, with
project-local names and the domain hypothesis used by subalgebras of fields,
from TauCeti/RingTheory/Ideal/MinimalPrime/Localization.lean and
TauCeti/RingTheory/DiscreteValuationRing/MinimalPrime.lean,
revision 30f41378f0cb1d569f51d8a4d0cb74aea8a80e44.
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.Submodule

/-!
# Reduced principal divisors at their minimal primes

The local DVR conclusion is proved from Noetherianity, an ambient domain,
nonvanishing of the generator, and a reduced quotient. No regular-local-ring
or henselization assumption is imported.
-/

namespace ZInQ.Contrib.Abhyankar

open IsLocalRing Ideal

/-- A radical ideal becomes the maximal ideal at each of its minimal primes. -/
theorem local_map_eq_maximalIdeal_of_radical
    {S : Type*} [CommRing S] {I P : Ideal S} [P.IsPrime]
    (hI : I.IsRadical) (hP : P ∈ I.minimalPrimes) :
    I.map (algebraMap S (Localization.AtPrime P)) =
      maximalIdeal (Localization.AtPrime P) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P),
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (A := Localization.AtPrime P) P I hP,
    ← IsLocalization.map_radical P.primeCompl (Localization.AtPrime P), hI.radical]

/-- A nonzero reduced principal divisor generates the maximal ideal at each minimal prime. -/
theorem local_maximalIdeal_eq_span
    {S : Type*} [CommRing S] {x : S} {P : Ideal S} [P.IsPrime]
    [IsReduced (S ⧸ Ideal.span {x})] (hP : P ∈ (Ideal.span {x}).minimalPrimes) :
    maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap S (Localization.AtPrime P) x} := by
  rw [← local_map_eq_maximalIdeal_of_radical
    ((Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance) hP,
    Ideal.map_span, Set.image_singleton]

/-- The localization of a Noetherian domain at a prime minimal over a nonzero
reduced principal divisor is a DVR, with that divisor as uniformizer. -/
theorem local_dvr_of_reduced_principal
    {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    {x : S} (hx : x ≠ 0) {P : Ideal S} [P.IsPrime]
    [IsReduced (S ⧸ Ideal.span {x})] (hP : P ∈ (Ideal.span {x}).minimalPrimes) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hm := local_maximalIdeal_eq_span hP
  have hxP : algebraMap S (Localization.AtPrime P) x ≠ 0 := by
    simpa only [map_zero] using
      (IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors).ne hx
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [isField_iff_maximalIdeal_eq, hm]
    simpa only [Ideal.span_singleton_eq_bot] using hxP
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr
    (⟨algebraMap S (Localization.AtPrime P) x, hm⟩ :
      (maximalIdeal (Localization.AtPrime P)).IsPrincipal)

end ZInQ.Contrib.Abhyankar
