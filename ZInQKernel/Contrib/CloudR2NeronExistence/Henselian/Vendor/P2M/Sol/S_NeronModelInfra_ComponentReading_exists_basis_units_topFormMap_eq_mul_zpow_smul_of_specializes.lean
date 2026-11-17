import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes.lean
Original Git blob: f7b2ee5c7c8f7824fdfd4811140e7199e45a3ca3
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 1 scopes originally left open at EOF.
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
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
    (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
    (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
    (hKU : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U; IsScalarTower K Γ(XK, U) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
      (schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
        T.e).1)
    (ωU : ⋀[Γ(XK, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U)))
    (hωU : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U ωU = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω) :
    ∃ (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
      (w : (T.Y.presheaf.stalk y₁)ˣ),
      letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U
      TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
        (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
            algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ T.n) •
          TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
            (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b') := by
  obtain ⟨b', w, m, h⟩ :=
    NeronModelInfra.ComponentReading.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
      ϖ hϖ K hω T y₁ hy₁ hgen halg₁
  have hm : m = T.n :=
    NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul ϖ hϖ K hω T y₁ hy₁ hgen halg₁ b' w m h
  exact ⟨b', w, hm ▸ h F U hU hKU hx ωU hωU⟩


end P2MW.S_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
