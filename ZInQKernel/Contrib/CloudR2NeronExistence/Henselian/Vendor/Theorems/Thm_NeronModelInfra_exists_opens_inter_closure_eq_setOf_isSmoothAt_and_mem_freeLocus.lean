import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus.lean
Original Git blob: f22a9d211fd55e122e25cfae6a8cff0dfa1c1ea3
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

h77_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem TensorProduct"

universe u

theorem NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = s)
    (hSk : ∀ s ∈ S, f s = IsLocalRing.closedPoint R)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ closure S})
    ∃ W : X.Opens, (W : Set X) ⊆ U ∧
      ((closure S ∩ (U : Set X)).Nonempty → (closure S ∩ (W : Set X)).Nonempty) ∧
      ∀ (y : X) (hyU : y ∈ U), y ∈ closure S →
        (y ∈ W ↔
          ∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
            𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
            (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
              [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
              Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
            (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
              Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
