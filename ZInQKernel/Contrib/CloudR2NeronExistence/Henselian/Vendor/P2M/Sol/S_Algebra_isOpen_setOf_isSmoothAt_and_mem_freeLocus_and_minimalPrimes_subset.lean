import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset.lean
Original Git blob: 66d5a4cbd916f9553a3dab49fd02b38c2e6efdeb
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

universe u

theorem solution
    {k : Type u} [Field k] {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (J : Ideal A)
    [Algebra k (A ⧸ J)] [Algebra.FiniteType k (A ⧸ J)] [IsReduced (A ⧸ J)]
    (S : Set (PrimeSpectrum (A ⧸ J)))
    (hdense : ∀ g : A ⧸ J, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K)) :
    IsOpen {𝔮 : PrimeSpectrum (A ⧸ J) | Algebra.IsSmoothAt k 𝔮.asIdeal ∧
      𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)} ∧
    ∀ 𝔮 : PrimeSpectrum (A ⧸ J), 𝔮.asIdeal ∈ minimalPrimes (A ⧸ J) →
      Algebra.IsSmoothAt k 𝔮.asIdeal ∧ 𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by
  classical
  haveI : Algebra.FinitePresentation k (A ⧸ J) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨?_, ?_⟩
  · have h1 : IsOpen (Algebra.smoothLocus k (A ⧸ J)) := Algebra.isOpen_smoothLocus
    have h2 : IsOpen (Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)) := Module.isOpen_freeLocus
    have : {𝔮 : PrimeSpectrum (A ⧸ J) | Algebra.IsSmoothAt k 𝔮.asIdeal ∧
        𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)} =
        Algebra.smoothLocus k (A ⧸ J) ∩ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by
      ext 𝔮; rfl
    rw [this]
    exact h1.inter h2
  · intro 𝔮 h𝔮
    refine ⟨Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField S hdense hsep 𝔮.asIdeal h𝔮, ?_⟩
    rw [Module.mem_freeLocus]
    haveI : Ring.KrullDimLE 0 (Localization.AtPrime 𝔮.asIdeal) :=
      Ring.KrullDimLE.of_isLocalization 𝔮.asIdeal h𝔮 (Localization.AtPrime 𝔮.asIdeal)
    letI hF : Field (Localization.AtPrime 𝔮.asIdeal) := Ring.KrullDimLE.isField_of_isReduced.toField
    exact Module.Free.of_divisionRing (Localization.AtPrime 𝔮.asIdeal) _


end P2MW.S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
