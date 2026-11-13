/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Modified for this contribution: the derivative upper-bound proof is stated
on genuine Mathlib DVRs and their ramification index, without the Tau Ceti
local-field wrapper, and uses the independently proved residue/no-cancellation
lemmas in Valuation.lean. Monogenic different identity is supplied by
Monogenic.lean. The uniformizer-generation/degree hypotheses are explicit.
Source revision: a6027b1d24fcb935c53bd5b50d11b40991cda418.
Source: TauCeti/NumberTheory/LocalField/Different/Eisenstein.lean.
-/
import ZInQKernel.Contrib.DifferentBound.Valuation
import ZInQKernel.Contrib.DifferentBound.Monogenic
import ZInQKernel.Contrib.DifferentBound.Degree

/-!
# The proved derivative estimate, and its exact local different consequence

This is the arithmetic part of the Serre bound. The first helpers expose the
generation and degree inputs; the finite-extension wrappers derive degree equals
ramification from a genuine generating uniformizer. No Hilbert formula is used.

This module does not assert that these inputs have been constructed for every
number-field completion. It is not a closed proof of global target T21 or of
`PkgI6.DifferentBound`.
-/

namespace ZInQ.Contrib.DifferentBound

open IsLocalRing Polynomial

section Derivative

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.IsTorsionFree A B] [(maximalIdeal B).LiesOver (maximalIdeal A)]

/-- The derivative of a monic polynomial of degree `e` evaluated at a uniformizer has valuation
at most `e - 1 + v_B(e)`. Every derivative term is included and cancellation is ruled out by
its distinct valuation residue modulo `e`. Zero coefficients and zero `(e : B)` are allowed. -/
theorem addVal_aeval_derivative_le
    {π : B} (hπ : Irreducible π) (f : A[X]) (hmo : f.Monic)
    (hdegree : f.natDegree = (maximalIdeal B).ramificationIdx A) :
    IsDiscreteValuationRing.addVal B (aeval π (derivative f)) ≤
      (((maximalIdeal B).ramificationIdx A - 1 : ℕ) : ℕ∞) +
        IsDiscreteValuationRing.addVal B ((maximalIdeal B).ramificationIdx A : B) := by
  have hdeg : 0 < f.natDegree := hdegree.symm ▸ dvr_ramificationIdx_pos
  let c : Fin f.natDegree → A := fun i ↦
    f.coeff ((i : ℕ) + 1) * (((i : ℕ) + 1 : ℕ) : A)
  have hsum : aeval π (derivative f) =
      ∑ i : Fin f.natDegree, algebraMap A B (c i) * π ^ (i : ℕ) := by
    rw [Polynomial.aeval_eq_sum_range'
      (Polynomial.natDegree_derivative_lt hdeg.ne') π]
    simp only [← Fin.sum_univ_eq_sum_range, Polynomial.coeff_derivative, Algebra.smul_def, c,
      Nat.cast_add, Nat.cast_one]
  let j : Fin f.natDegree := ⟨f.natDegree - 1, by omega⟩
  have hsub : f.natDegree - 1 + 1 = f.natDegree := by omega
  have hc : c j = ((maximalIdeal B).ramificationIdx A : A) := by
    dsimp [c, j]
    rw [hsub, coeff_natDegree, hmo.leadingCoeff, one_mul, hdegree]
  have hj : (j : ℕ) = (maximalIdeal B).ramificationIdx A - 1 := by
    simp only [j, hdegree]
  rw [hsum, addVal_sum_algebraMap_mul_pow hπ (by omega)]
  calc
    _ ≤ (maximalIdeal B).ramificationIdx A • IsDiscreteValuationRing.addVal A (c j) +
        ((j : ℕ) : ℕ∞) := Finset.inf_le (f := fun i : Fin f.natDegree ↦
          (maximalIdeal B).ramificationIdx A • IsDiscreteValuationRing.addVal A (c i) +
            ((i : ℕ) : ℕ∞)) (Finset.mem_univ j)
    _ = _ := by
      rw [hc, hj, ← addVal_algebraMap, map_natCast, add_comm]

end Derivative

section Different

variable (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
  [IsIntegralClosure B A L] [Module.IsTorsionFree A B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [(maximalIdeal B).LiesOver (maximalIdeal A)]

include K L

/-- The exact local ideal bound follows from a monogenic uniformizer whose minimal polynomial
has the actual ramification degree. This is a proved structural-case theorem, not the assertion
that such a uniformizer exists for every extension. The zero characteristic-divisor case is
included (its right-hand ideal is zero). -/
theorem differentIdeal_bound_of_monogenic_uniformizer
    {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin A {π} = ⊤)
    (hdegree : (minpoly A π).natDegree = (maximalIdeal B).ramificationIdx A) :
    differentIdeal A B ∣ maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
      Ideal.span {((maximalIdeal B).ramificationIdx A : B)} := by
  have hd := differentIdeal_eq_span_aeval_derivative_minpoly A K L B π hgen
  have hmo := minpoly.monic (IsIntegralClosure.isIntegral A L π)
  have hpow (n : ℕ) : maximalIdeal B ^ n = Ideal.span {π ^ n} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [hd, hpow, Ideal.span_singleton_mul_span_singleton,
    Ideal.dvd_span_singleton, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd,
    IsDiscreteValuationRing.addVal_mul, hπ.addVal_pow]
  exact addVal_aeval_derivative_le hπ (minpoly A π) hmo hdegree

/-- The same proved local bound as a natural-number multiplicity inequality, when the
ramification index has nonzero image in the extension ring. Characteristic zero supplies this
condition after ramification positivity; it is not a hypothesis added to T21. -/
theorem multiplicity_differentIdeal_le_of_monogenic_uniformizer
    {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin A {π} = ⊤)
    (hdegree : (minpoly A π).natDegree = (maximalIdeal B).ramificationIdx A)
    (he : ((maximalIdeal B).ramificationIdx A : B) ≠ 0) :
    multiplicity (maximalIdeal B) (differentIdeal A B) ≤
      (maximalIdeal B).ramificationIdx A - 1 +
        multiplicity (maximalIdeal B)
          (Ideal.span {((maximalIdeal B).ramificationIdx A : B)}) := by
  have hd := differentIdeal_eq_span_aeval_derivative_minpoly A K L B π hgen
  have hmo := minpoly.monic (IsIntegralClosure.isIntegral A L π)
  have hderiv : aeval π (derivative (minpoly A π)) ≠ 0 := by
    intro hz
    have hD : differentIdeal A B ≠ ⊥ := by
      have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L),
        coeIdeal_differentIdeal (A := A) (K := K)]
      simp
    exact hD (by rw [hd, hz, Ideal.span_singleton_eq_bot])
  have hval := addVal_aeval_derivative_le hπ (minpoly A π) hmo hdegree
  rw [addVal_eq_multiplicity_span_singleton hderiv,
    addVal_eq_multiplicity_span_singleton he] at hval
  rw [hd]
  exact_mod_cast hval

/-- The degree comparison is now discharged: a genuine generating uniformizer suffices
for the Serre ideal bound in any finite separable extension of DVRs. -/
theorem differentIdeal_bound_of_generating_uniformizer [Module.Finite A B]
    {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin A {π} = ⊤) :
    differentIdeal A B ∣ maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
      Ideal.span {((maximalIdeal B).ramificationIdx A : B)} :=
  differentIdeal_bound_of_monogenic_uniformizer A K L B hπ hgen
    (minpoly_natDegree_eq_ramificationIdx_of_generating_uniformizer A K L B hπ hgen)

/-- The numeric Serre bound for a genuine generating uniformizer, with degree=e proved rather
than supplied. The nonzero integer-cast condition is necessary to make this a finite bound. -/
theorem multiplicity_differentIdeal_le_of_generating_uniformizer [Module.Finite A B]
    {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin A {π} = ⊤)
    (he : ((maximalIdeal B).ramificationIdx A : B) ≠ 0) :
    multiplicity (maximalIdeal B) (differentIdeal A B) ≤
      (maximalIdeal B).ramificationIdx A - 1 +
        multiplicity (maximalIdeal B)
          (Ideal.span {((maximalIdeal B).ramificationIdx A : B)}) :=
  multiplicity_differentIdeal_le_of_monogenic_uniformizer A K L B hπ hgen
    (minpoly_natDegree_eq_ramificationIdx_of_generating_uniformizer A K L B hπ hgen) he

end Different

end ZInQ.Contrib.DifferentBound
