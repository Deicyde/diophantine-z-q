import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq.lean
Original Git blob: 8e88e0a6c5ba176c25212340a48ac4dfb96145ab
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    {X Y Z : Scheme.{u}} (gZ : Z ⟶ Spec (CommRingCat.of A)) (gY : Y ⟶ Spec (CommRingCat.of B))
    (gX : X ⟶ Spec (CommRingCat.of C))
    (ψ : Y ⟶ Z) (hψ : ψ ≫ gZ = gY ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (d : ℕ)
    (θψ : (Scheme.Modules.pullback ψ).obj ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d) ⟶ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gY) d)
    (hθψ : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : IsAffineOpen W) (hWU : W ≤ ψ ⁻¹ᵁ U),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gZ) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gY) W
        letI : Algebra Γ(Z, U) Γ(Y, W) := (ψ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(Y, W)] [IsScalarTower A B Γ(Y, W)] [IsScalarTower A Γ(Z, U) Γ(Y, W)]
          (η : ⋀[Γ(Z, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gZ).obj (op U))),
          ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gY) d).presheaf.map (homOfLE hWU).op
              (θψ.app (ψ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection ψ ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gZ) d U η))) =
            (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gY) d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Z, U) Γ(Y, W) d η))
    (θφ : (Scheme.Modules.pullback φ).obj ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gY) d) ⟶ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d)
    (hθφ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gY) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra B Γ(X, W)] [IsScalarTower B C Γ(X, W)] [IsScalarTower B Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gY).obj (op U))),
          ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d).presheaf.map (homOfLE hWU).op
              (θφ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gY) d U η))) =
            (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gX) d W (NeronModelInfra.TopFormOrder.topFormMap B C Γ(Y, U) Γ(X, W) d η))
    (θ : (Scheme.Modules.pullback (φ ≫ ψ)).obj ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d) ⟶ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d)
    (hθ : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ (φ ≫ ψ) ⁻¹ᵁ U),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gZ) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W
        letI : Algebra Γ(Z, U) Γ(X, W) := ((φ ≫ ψ).appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A C Γ(X, W)] [IsScalarTower A Γ(Z, U) Γ(X, W)]
          (η : ⋀[Γ(Z, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gZ).obj (op U))),
          ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d).presheaf.map (homOfLE hWU).op
              (θ.app ((φ ≫ ψ) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gZ) d U η))) =
            (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gX) d W (NeronModelInfra.TopFormOrder.topFormMap A C Γ(Z, U) Γ(X, W) d η)) :
    θ = ((Scheme.Modules.pullbackComp φ ψ).app ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d)).inv ≫
      (Scheme.Modules.pullback φ).map θψ ≫ θφ := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
