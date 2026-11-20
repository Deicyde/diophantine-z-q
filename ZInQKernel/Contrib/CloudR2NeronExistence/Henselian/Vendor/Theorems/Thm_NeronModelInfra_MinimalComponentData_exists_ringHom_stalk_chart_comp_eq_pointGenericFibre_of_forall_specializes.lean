import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes.lean
Original Git blob: dcfc599a1ac0f8e23f240ed758025c3bb7c189f6
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.MinimalComponentData.exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (ξ : ↥X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : ↥X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ)
    [Algebra R (X.presheaf.stalk ξ)]
    (halgX : X.fromSpecStalk ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ))))
    (F : Type u) [Field F] [Algebra (X.presheaf.stalk ξ) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (X.presheaf.stalk ξ) F] [IsScalarTower R K F]
    (hinj : Function.Injective (algebraMap (X.presheaf.stalk ξ) F)) :
    ∃ (c : D.ι) (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ξ))
      (_ : (j c).1.base ⟨(D.C c).y, hyV c⟩ = ξ)
      (_ : Function.Bijective φ) (_ : IsLocalHom φ)
      (_ : letI := (D.C c).algebra; φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) = algebraMap R (X.presheaf.stalk ξ))
      (algF : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : letI : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) F := ((algebraMap (X.presheaf.stalk ξ) F).comp φ).toAlgebra
           IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F),
      letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) (D.C c).U
      letI := (D.C c).algebraU
      letI : Algebra Γ(XK, (D.C c).U) F :=
        ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
      Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, (D.C c).U) F)) ≫ (D.C c).hU.fromSpec =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨X.fromSpecStalk ξ, halgX⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ)))) f))
          e).1 := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
