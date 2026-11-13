import ZInQKernel.Contrib.DifferentBound.Local

/-!
# The unramified-tower step of the Serre bound

The equalities of the actual different and actual ramification index are proved
from Mathlib's transitivity and unramifiedness theorems. No bound is an input.
Existence of the unramified intermediate DVR is a separate construction, not
asserted here. This module does not close global target T21.
-/

namespace ZInQ.Contrib.DifferentBound

open IsLocalRing
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- A finite separable extension of DVRs unramified at its maximal ideal has unit different. -/
theorem differentIdeal_eq_top_of_isUnramifiedAt
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra.IsUnramifiedAt A (maximalIdeal B)] : differentIdeal A B = ⊤ := by
  have hnot : ¬ maximalIdeal B ∣ differentIdeal A B := not_dvd_differentIdeal_iff.mpr
    (inferInstance : Algebra.IsUnramifiedAt A (maximalIdeal B))
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hD hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hn
  by_cases hn0 : n = 0
  · simpa [hn0] using hn
  · exact (hnot (hn ▸ dvd_pow_self (maximalIdeal B) hn0)).elim

section Tower

variable (A U B : Type*)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A U] [Algebra U B] [Algebra A B] [IsScalarTower A U B]
  [Module.Finite A U] [Module.Finite U B] [Module.Finite A B]
  [Module.IsTorsionFree A U] [Module.IsTorsionFree U B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [(maximalIdeal B).LiesOver (maximalIdeal U)]
  [Algebra.IsUnramifiedAt A (maximalIdeal U)]

omit [IsDomain A] [IsDiscreteValuationRing A] [Module.Finite U B] [Module.Finite A B]
  [Module.IsTorsionFree A U] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- An unramified intermediate DVR leaves the actual ramification index unchanged. -/
theorem ramificationIdx_eq_of_unramified_tower :
    (maximalIdeal B).ramificationIdx A = (maximalIdeal B).ramificationIdx U := by
  have h := Ideal.ramificationIdx_tower (R := A) (maximalIdeal U) (maximalIdeal B)
  rw [Ideal.ramificationIdx_eq_one (maximalIdeal U) A, one_mul] at h
  exact h

omit [(maximalIdeal B).LiesOver (maximalIdeal U)] in
/-- An unramified intermediate DVR leaves the actual different ideal unchanged. -/
theorem differentIdeal_eq_of_unramified_tower : differentIdeal A B = differentIdeal U B := by
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal (A := A) (B := U) B
  have : Algebra.IsSeparable (FractionRing A) (FractionRing U) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (FractionRing A) (FractionRing U) (FractionRing B)
  have htop : differentIdeal A U = ⊤ := differentIdeal_eq_top_of_isUnramifiedAt A U
  simpa only [htop, Ideal.map_top, Ideal.mul_top] using h

/-- Serre's local bound through a supplied unramified tower. The top extension must be supplied
with a genuine generating uniformizer of ramification degree; this structural existence is not
a bound hypothesis and remains a separate obligation. -/
theorem differentIdeal_bound_of_unramified_tower
    [IsIntegralClosure B U (FractionRing B)]
    [FiniteDimensional (FractionRing U) (FractionRing B)]
    [Algebra.IsSeparable (FractionRing U) (FractionRing B)]
    {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin U {π} = ⊤)
    (htot : (maximalIdeal B).ramificationIdx U =
      Module.finrank (FractionRing U) (FractionRing B)) :
    differentIdeal A B ∣ maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
      Ideal.span {((maximalIdeal B).ramificationIdx A : B)} := by
  rw [differentIdeal_eq_of_unramified_tower A U B,
    ramificationIdx_eq_of_unramified_tower A U B]
  apply differentIdeal_bound_of_monogenic_uniformizer U (FractionRing U) (FractionRing B) B
    hπ hgen
  exact (minpoly_natDegree_eq_finrank_of_ring_adjoin_eq_top
    U (FractionRing U) (FractionRing B) B π hgen).trans htot.symm

end Tower

end ZInQ.Contrib.DifferentBound
