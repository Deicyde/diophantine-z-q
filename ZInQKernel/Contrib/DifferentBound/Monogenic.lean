/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Chris Birkbeck

Modified for this contribution: extracted the single-generator fraction-field
argument and monogenic different identity only, with owned names and pinned
Mathlib 4.35 imports. No generator-existence theorem is assumed or ported here.
Source revision: a6027b1d24fcb935c53bd5b50d11b40991cda418.
Sources: TauCeti/FieldTheory/IntermediateField/Adjoin/EqTop.lean;
TauCeti/RingTheory/DedekindDomain/Different/Monogenic.lean.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Identifying the actual monogenic different

The hypothesis `A[x] = B` is a structural generation hypothesis, not a different
bound. Fraction-field generation is proved, not added as a second assumption.
These lemmas do not assert that a global number-field integer ring is monogenic.
-/

namespace ZInQ.Contrib.DifferentBound

open Polynomial

/-- A ring generator also generates its fraction field over an intermediate base field. -/
theorem field_adjoin_eq_top_of_ring_adjoin_eq_top
    {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
    [FiniteDimensional K L] {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    Algebra.adjoin K {algebraMap B L x} = ⊤ := by
  rw [← IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
    (fun y _ ↦ IsAlgebraic.of_finite K y)]
  have hle : Algebra.adjoin A {x} ≤
      ((IntermediateField.adjoin K {algebraMap B L x}).toSubalgebra.restrictScalars A).comap
        (IsScalarTower.toAlgHom A B L) :=
    Algebra.adjoin_le fun y hy ↦ by
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) y
  exact div_mem (hle (hx.ge Algebra.mem_top)) (hle (hx.ge Algebra.mem_top))

/-- The genuine different of a monogenic integral closure is its minimal-polynomial derivative.
The order conductor becomes the unit ideal; fraction-field generation is derived above. -/
theorem differentIdeal_eq_span_aeval_derivative_minpoly
    (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : B) (hx : Algebra.adjoin A {x} = ⊤) :
    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hK : Algebra.adjoin K {algebraMap B L x} = ⊤ :=
    field_adjoin_eq_top_of_ring_adjoin_eq_top hx
  rw [← conductor_mul_differentIdeal A K L x hK,
    conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul]

/-- A supplied ring generator has minimal-polynomial degree equal to the genuine
fraction-field degree. This comparison is derived from the integral/fraction maps, not assumed. -/
theorem minpoly_natDegree_eq_finrank_of_ring_adjoin_eq_top
    (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : B) (hx : Algebra.adjoin A {x} = ⊤) :
    (minpoly A x).natDegree = Module.finrank K L := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hAx := IsIntegralClosure.isIntegral A L x
  have hK := field_adjoin_eq_top_of_ring_adjoin_eq_top (K := K) (L := L) hx
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite K _) hK
  have hpgen : pb.gen = algebraMap B L x := rfl
  calc
    (minpoly A x).natDegree = (minpoly K (algebraMap B L x)).natDegree := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
        (minpoly.monic hAx).natDegree_map]
    _ = pb.dim := by simpa only [hpgen] using pb.natDegree_minpoly
    _ = Module.finrank K L := pb.finrank.symm

end ZInQ.Contrib.DifferentBound
