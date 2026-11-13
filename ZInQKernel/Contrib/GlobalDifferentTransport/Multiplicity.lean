/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The single-completion ingredients are selected from TauCeti revision
 a6027b1d24fcb935c53bd5b50d11b40991cda418.
The multiplicity proof here uses the all-power comparison rather than importing
TauCeti's ideal-factorization proof in AdicValuation/Multiplicity.lean.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Completion

/-!
# Multiplicity in a completed integer ring

The all-power comparison implies equality of finite multiplicities, with
nonzeroness proved for the extended ideal. The ring of completed integers has
ramification index one over the affine model at the selected prime. This does
not assert that this generally infinite ring extension is finite or unramified
in the essentially-finite-type sense.
-/

public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain

namespace GlobalDifferentTransport

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/-- Extension to the completed integer ring preserves finite ideal multiplicity at `v`. -/
theorem multiplicity_map_adicCompletionIntegers (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (I.map (algebraMap R (v.adicCompletionIntegers K))) =
      multiplicity v.asIdeal I := by
  have hlocal : FiniteMultiplicity
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (I.map (algebraMap R (v.adicCompletionIntegers K))) :=
    FiniteMultiplicity.of_not_isUnit
      (mt Ideal.isUnit_iff.mp
        (Ideal.IsPrime.ne_top (inferInstance :
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).IsPrime)))
      (Ideal.map_ne_bot_of_ne_bot hI)
  have hglobal := FiniteMultiplicity.of_prime_left v.prime hI
  have hle (n : ℕ) :
      n ≤ multiplicity (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
          (I.map (algebraMap R (v.adicCompletionIntegers K))) ↔
        n ≤ multiplicity v.asIdeal I :=
    hlocal.pow_dvd_iff_le_multiplicity.symm.trans
      ((pow_dvd_map_adicCompletionIntegers_iff v I n).trans
        hglobal.pow_dvd_iff_le_multiplicity)
  exact le_antisymm ((hle _).mp le_rfl) ((hle _).mpr le_rfl)

/-- The completed maximal ideal lies over exactly the selected global prime. -/
theorem maximalIdeal_adicCompletionIntegers_liesOver :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).LiesOver v.asIdeal :=
  (Ideal.liesOver_iff _ _).mpr
    (under_maximalIdeal_adicCompletionIntegers v).symm

/-- The ideal-power ramification index from the affine model to its completion is one. -/
theorem ramificationIdx'_adicCompletionIntegers_eq_one :
    Ideal.ramificationIdx' v.asIdeal
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) = 1 := by
  rw [← map_asIdeal_adicCompletionIntegers v]
  exact Ideal.ramificationIdx'_map_self_eq_one
    (by rw [map_asIdeal_adicCompletionIntegers v]; exact Ideal.IsPrime.ne_top')
    (Ideal.map_ne_bot_of_ne_bot v.ne_bot)

/-- Mathlib's length-defined ramification index from the affine model to its completion
is also one. No finite-module assertion about that extension is used. -/
theorem ramificationIdx_adicCompletionIntegers_eq_one :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).ramificationIdx R = 1 := by
  let := maximalIdeal_adicCompletionIntegers_liesOver (K := K) v
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) v.ne_bot]
  exact ramificationIdx'_adicCompletionIntegers_eq_one v

end GlobalDifferentTransport
