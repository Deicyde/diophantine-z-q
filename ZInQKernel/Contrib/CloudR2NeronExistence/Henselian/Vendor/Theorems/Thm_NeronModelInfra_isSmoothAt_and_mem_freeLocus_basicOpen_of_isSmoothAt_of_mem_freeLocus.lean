import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus.lean
Original Git blob: ec35a50be13b79da1b49eee8a97445773e78cecf
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (C : Set X) (hC : ∀ y ∈ C, f y = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) (h : Γ(X, U)) (y : X) (hyU : y ∈ U) (hyh : y ∈ X.basicOpen h) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    letI : Algebra R Γ(X, X.basicOpen h) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ C})
    let J' : Ideal Γ(X, X.basicOpen h) :=
      PrimeSpectrum.vanishingIdeal ((fun z : X.basicOpen h => (hU.basicOpen h).primeIdealOf z) ''
        {z : X.basicOpen h | (z : X) ∈ C})
    (∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
      𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
      (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
        Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) →
    ∀ (𝔮' : Ideal (Γ(X, X.basicOpen h) ⧸ J')) [𝔮'.IsPrime],
      𝔮'.comap (Ideal.Quotient.mk J') = ((hU.basicOpen h).primeIdealOf ⟨y, hyh⟩).asIdeal →
      (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')]
        [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, X.basicOpen h) ⧸ J')],
        Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮') ∧
      (⟨𝔮', ‹_›⟩ : PrimeSpectrum (Γ(X, X.basicOpen h) ⧸ J')) ∈
        Module.freeLocus (Γ(X, X.basicOpen h) ⧸ J')
          ((Γ(X, X.basicOpen h) ⧸ J') ⊗[Γ(X, X.basicOpen h)] Ω[Γ(X, X.basicOpen h)⁄R]) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
