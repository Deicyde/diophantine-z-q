import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback.lean
Original Git blob: e750e6b2ef4b05e30db20ba2afa85671586278af
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

h77_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback.AlgebraicGeometry"

universe u v

namespace AlgebraicGeometry
h77_bridge_namespace
h77_export "AlgebraicGeometry" "isPushout_appTop_of_isPullback Scheme.Hom IsAffine isPullback_morphismRestrict Spec Spec.map Scheme Scheme.Hom.appTop Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop IsAffineOpen Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top Scheme.ΓSpecIso_naturality IsAffineHom Scheme.Opens.ι_appTop Scheme.ΓSpecIso"
h77_open "AlgebraicGeometry"

namespace Scheme h77_export "AlgebraicGeometry.Scheme" "Hom Γ topIso_hom topIso Hom.appTop Opens.topIso_hom Hom.comp_appTop Opens Hom.appLE_map Hom.app_eq_appLE Hom.resLE_eq_morphismRestrict Hom.resLE_app_top ΓSpecIso_naturality Opens.ι_appTop ΓSpecIso" namespace Hom h77_export "AlgebraicGeometry.Scheme.Hom" "appTop comp_appTop appLE_map app_eq_appLE resLE_eq_morphismRestrict resLE_app_top appLE sectionsAlgebra" end Scheme.Hom
h77_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in
set_option backward.isDefEq.respectTransparency false in

theorem Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback_aux
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (U : Y.Opens) :
    (U.ι ≫ gY).appTop ≫ U.topIso.hom = gY.appLE ⊤ U le_top := by
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, Category.assoc,
    ← Functor.map_comp, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

end AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (φ ⁻¹ᵁ U) ∧
      letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gY) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) (φ ⁻¹ᵁ U)
      letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      ∀ [Algebra A Γ(X, φ ⁻¹ᵁ U)] [IsScalarTower A B Γ(X, φ ⁻¹ᵁ U)]
        [IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)],
        Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
  haveI hφaff : IsAffineHom φ :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hφ.flip inferInstance
  have hV : IsAffineOpen (φ ⁻¹ᵁ U) := hU.preimage φ
  refine ⟨hV, ?_⟩
  intro algA ist₁ ist₂

  have sq : IsPullback (φ ∣_ U) ((φ ⁻¹ᵁ U).ι ≫ gX) (U.ι ≫ gY)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    (isPullback_morphismRestrict φ U).paste_vert hφ
  haveI : IsAffine U := hU
  haveI : IsAffine (φ ⁻¹ᵁ U) := hV
  have H := isPushout_appTop_of_isPullback sq.flip
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gY) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) (φ ⁻¹ᵁ U)
  letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  refine (CommRingCat.isPushout_iff_isPushout (R := A) (R' := B) (S := Γ(Y, U))
    (S' := Γ(X, φ ⁻¹ᵁ U))).mp ?_
  have e₁ : CommRingCat.ofHom (algebraMap A Γ(Y, U)) =
      (Scheme.ΓSpecIso (.of A)).inv ≫ gY.appLE ⊤ U le_top := rfl
  have e₂ : CommRingCat.ofHom (algebraMap B Γ(X, φ ⁻¹ᵁ U)) =
      (Scheme.ΓSpecIso (.of B)).inv ≫ gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top := rfl
  have e₃ : CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)) =
      φ.appLE U (φ ⁻¹ᵁ U) le_rfl := rfl
  refine H.of_iso (Scheme.ΓSpecIso (.of A)) (Scheme.ΓSpecIso (.of B)) U.topIso (φ ⁻¹ᵁ U).topIso
    ?_ ?_ ?_ ?_
  · exact Scheme.ΓSpecIso_naturality _
  · rw [e₁, Iso.hom_inv_id_assoc]
    exact Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback_aux gY U
  · rw [e₂, Iso.hom_inv_id_assoc]
    exact Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback_aux gX (φ ⁻¹ᵁ U)
  · rw [e₃, ← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]


end P2MW.S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
