/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Units.LocalPowerClass), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Units.LocalPowerClass`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Units.LocalPowerClass
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Frobenius.Kummer.LocalUnit
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import ZInQKernel.Contrib.TauCeti.Backport.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import Mathlib.RingTheory.DedekindDomain.SInteger
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Places.UnitPowerClasses
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Units.SUnit.Basic
import ZInQKernel.Contrib.TauCeti.RingTheory.Valuation.UnitGroup

public noncomputable section

open IsDedekindDomain NumberField TauCeti
namespace Set

variable {K : Type*} [Field K] [NumberField K]
  (S T : Set (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)

/-- If the `S`-units surject onto the local unit `n`-th power classes at `T`, then every family
of local units at the places of `T` agrees with a single `S`-unit up to `n`-th powers. -/
theorem exists_mem_unit_of_unitLocalPowerClassMap_surjective
    {n : ℕ} (hsurj : Function.Surjective (unitLocalPowerClassMap S T hST n))
    (y : (v : T) → (v.1.adicCompletion K)ˣ) (hy : ∀ v, Valued.v (y v : v.1.adicCompletion K) = 1) :
    ∃ u ∈ S.unit K, ∀ v : T,
      (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u)⁻¹ * y v ∈
        (powMonoidHom n).range := by
  obtain ⟨u, hu⟩ := hsurj fun v ↦
    QuotientGroup.mk
      ⟨y v, (HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v.1).2 (hy v)⟩
  refine ⟨u, u.2, fun v ↦ ?_⟩
  obtain ⟨b, hb⟩ := QuotientGroup.eq.1 ((unitLocalPowerClassMap_apply _ _ _ _ _ _).symm.trans
    (congrFun hu v))
  exact ⟨b, congrArg Subtype.val hb⟩

end Set

end
