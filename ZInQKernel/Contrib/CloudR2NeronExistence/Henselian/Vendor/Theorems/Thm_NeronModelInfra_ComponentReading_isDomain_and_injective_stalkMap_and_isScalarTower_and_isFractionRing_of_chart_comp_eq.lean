import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq.lean
Original Git blob: 29a351a489d45bd7b0d67ce60d132b5f347840cd
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq

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

open CategoryTheory CategoryTheory.Limits Opposite open ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry hiding isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict open NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.ComponentReading.isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
    letI := T.algebra
    letI φ : T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩) ⟶ T.Y.presheaf.stalk T.y :=
      u.1.stalkMap ⟨T.y, hyW⟩ ≫ (W.stalkIso ⟨T.y, hyW⟩).hom
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) := φ.hom.toAlgebra
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) :=
      ((algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y))).comp φ.hom).toAlgebra
    letI : Algebra R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) := stalkAlgebra T'.f (u.1.base ⟨T.y, hyW⟩)
    IsDomain (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) ∧
      Function.Injective φ.hom ∧
      IsScalarTower R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) ∧
      IsFractionRing (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
