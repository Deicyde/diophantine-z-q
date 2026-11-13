/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.AutomorphismAction
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import ZInQKernel.Contrib.TauCeti.NumberTheory.RamificationInertia.SeparableDegree
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia

public section
noncomputable section

section
open IsDedekindDomain Module NumberField
open scoped NumberField Pointwise AdicCompletionExtension
namespace IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
variable [NumberField K] (v : HeightOneSpectrum (𝒪 K))
variable {v}
variable (v) (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]
variable {v w}
variable (v w) [IsAbelianGalois K L]

/-- **A completion of an abelian extension is abelian.** For `L/K` abelian the local extension
`L_w/K_v` at a finite place `w` of `L` is an abelian Galois extension. -/
-- The Galois group of `L_w/K_v` is the decomposition group of `w`, a subgroup of `Gal(L/K)`.
theorem isAbelianGalois_adicCompletion :
    IsAbelianGalois (v.adicCompletion K) (w.adicCompletion L) :=
  have := (decompositionEquiv v w).surjective.isMulCommutative
  ⟨⟩

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isAbelianGalois_adicCompletion

end IsDedekindDomain.HeightOneSpectrum
end

end
end
