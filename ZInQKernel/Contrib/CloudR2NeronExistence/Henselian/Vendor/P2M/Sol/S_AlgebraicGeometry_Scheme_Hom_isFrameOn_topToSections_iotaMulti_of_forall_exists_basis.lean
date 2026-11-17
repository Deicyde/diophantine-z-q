import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis.lean
Original Git blob: cdce93b544dc7e7dcea16613a280967ea2dcfd7f
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace WedgeFrameGC7
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W') : Type u) :=
  ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE i).op).hom w

noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) : Type u)) :
    (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W') : Type u) :=
  (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val.presheaf.map (homOfLE i).op s

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    res f i ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W w) = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f))).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma algebraMap_sections_eq {U W : X.Opens} (h : W ≤ U) (a : A) :
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) U
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) W
    algebraMap A Γ(X, W) a = (X.presheaf.map (homOfLE h).op).hom (algebraMap A Γ(X, U) a) := by
  have := congrArg (fun φ => φ.hom a) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f).naturality (homOfLE h).op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp] at this
  exact this

end WedgeFrameGC7

set_option backward.isDefEq.respectTransparency false in
open WedgeFrameGC7 in
theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) U
    ∀ (η : Fin d → Ω[Γ(X, U)⁄A]),
      (∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) W
        letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
        ∀ [IsScalarTower A Γ(X, U) Γ(X, W)],
          ∃ b : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]),
            ∀ i, b i = KaehlerDifferential.map A A Γ(X, U) Γ(X, W) (η i)) →
      Scheme.Modules.IsFrameOn ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U (exteriorPower.ιMulti Γ(X, U) d η)) U := by
  letI algU := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) U
  intro η hη
  classical

  let e : Fin d → Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), U) := fun i =>
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) U (show ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U) : Type u) from η i)

  have he : ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W),
        ∀ i, b i = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).presheaf.map (homOfLE hW).op (e i) := by
    intro W hW hWaff
    letI algW : Algebra A Γ(X, W) := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) W
    letI algUW : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    haveI : IsScalarTower A Γ(X, U) Γ(X, W) :=
      IsScalarTower.of_algebraMap_eq fun a => algebraMap_sections_eq f hW a
    obtain ⟨b, hb⟩ := hη W hW hWaff
    have hbij := AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hWaff
    let τ : (Ω[Γ(X, W)⁄A]) ≃ₗ[Γ(X, W)] (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) : Type u) :=
      LinearEquiv.ofBijective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W) hbij
    refine ⟨b.map τ, fun i => ?_⟩
    rw [Module.Basis.map_apply, hb]
    change (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W (pmap f hW (show ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op U) : Type u) from η i)) = _
    rw [← res_toSh]
    rfl

  have he' := AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f) e he
  have h9 := AlgebraicGeometry.Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f)) (U := U) e he'

  have hts : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U (exteriorPower.ιMulti Γ(X, U) d η) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X d).obj (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val)).app (op U)).hom
        (show ((Scheme.Modules.presheafExteriorPower X d).obj (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val).obj (op U) from
          exteriorPower.ιMulti Γ(X, U) d e) := by
    show (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X d).obj (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val)).app (op U)).hom
        (exteriorPower.map d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) U) (exteriorPower.ιMulti Γ(X, U) d η)) = _
    rw [exteriorPower.map_apply_ιMulti]
    rfl
  rw [hts]
  exact h9


end P2MW.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
