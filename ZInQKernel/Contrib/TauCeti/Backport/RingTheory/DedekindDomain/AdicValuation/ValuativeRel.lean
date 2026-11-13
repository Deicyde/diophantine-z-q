/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel`.
module

public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Uniformizer
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.NormalizedValuation
public import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

public section
noncomputable section

section
open ValuativeRel Valued.integer
open scoped WithZero
namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- A unit of the completion `K_v` is a uniformizer exactly when its adic valuation `Valued.v` is
`exp (-1)`. -/
theorem isUniformizer_iff_valued_eq_exp_neg_one [Finite (R ⧸ v.asIdeal)]
    {π : (v.adicCompletion K)ˣ} :
    TauCeti.IsUniformizer (v.adicCompletion K) π ↔
      Valued.v (π : v.adicCompletion K) = WithZero.exp (-1) := by
  -- The normalized valuation of `π` is the inverse of its adic valuation.
  have hπ : (TauCeti.normalizedValuation (v.adicCompletion K) π : ℤᵐ⁰) =
      (Valued.v (π : v.adicCompletion K))⁻¹ := by
    rw [← TauCeti.normalizedValuationWithZero_coe, normalizedValuationWithZero_adicCompletion]
  -- What remains is a normalization of `ℤᵐ⁰` values.
  rw [TauCeti.isUniformizer_def, ← WithZero.coe_inj, hπ]
  simp [inv_eq_iff_eq_inv, ← WithZero.exp_eq_coe_ofAdd]

end IsDedekindDomain.HeightOneSpectrum
end

end
end
