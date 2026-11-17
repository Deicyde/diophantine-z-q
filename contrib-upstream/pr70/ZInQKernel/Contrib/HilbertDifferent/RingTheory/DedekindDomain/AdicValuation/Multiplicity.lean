/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/Multiplicity.lean
Original SHA-256: 1e3d8db91697b96744ee844ace247c454a74d5208fde538f343606991e7aa29b
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/DedekindDomain/AdicValuation/Multiplicity.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.NumberTheory.RamificationInertia.Ramification
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.Completion
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/- The coefficient at `v` of a nonzero ideal equals the coefficient at the maximal ideal after
extension to the integer ring of the `v`-adic completion. -/
@[simp]
theorem multiplicity_map_adicCompletionIntegers (v : HeightOneSpectrum R)
    (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (I.map (algebraMap R (v.adicCompletionIntegers K))) =
      multiplicity v.asIdeal I := by
  let B := v.adicCompletionIntegers K
  let P : Ideal B := IsLocalRing.maximalIdeal B
  have hmap : Ideal.map (algebraMap R B) v.asIdeal = P :=
    v.map_asIdeal_adicCompletionIntegers (K := K)
  have hP : P ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hPprime : P.IsPrime := inferInstance
  have : P.LiesOver v.asIdeal :=
    (Ideal.liesOver_iff_dvd_map hPprime.ne_top).2
      (by rw [hmap])
  have hidx : Ideal.ramificationIdx' v.asIdeal P = 1 := by
    rw [← hmap]
    exact Ideal.ramificationIdx'_map_self_eq_one
      (by rw [hmap]; exact hPprime.ne_top)
      (by rw [hmap]; exact hP)
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hI
    v.irreducible (Ideal.prime_of_isPrime hP hPprime).irreducible hP
  rw [hidx, Nat.cast_one, one_mul,
    (FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime hP hPprime)
        (Ideal.map_ne_bot_of_ne_bot hI)).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left v.prime hI).emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

end IsDedekindDomain.HeightOneSpectrum

end
