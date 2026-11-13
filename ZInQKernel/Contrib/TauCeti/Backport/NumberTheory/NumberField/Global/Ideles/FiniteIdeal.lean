/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

public section

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  IsDedekindDomain.FiniteAdeleRing NumberField NumberField.InfinitePlace
open scoped NumberField
namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The fractional ideal of an idele concentrated at one finite place, with a coordinate of
valuation `exp (-1)` there (a uniformizer), is the prime of that place. -/
theorem toFractionalIdeal_toFiniteIdele_ofAdicCompletion_of_eq_exp_neg_one
    (v : HeightOneSpectrum R) {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = WithZero.exp (-1)) :
    toFractionalIdeal (IdeleGroup.toFiniteIdele R K (IdeleGroup.ofAdicCompletion R K v u)) =
      v.unitOfPrime K := by
  rw [toFractionalIdeal_toFiniteIdele_ofAdicCompletion, hu, WithZero.log_exp, neg_neg, zpow_one]

end IsDedekindDomain.HeightOneSpectrum
end

end
