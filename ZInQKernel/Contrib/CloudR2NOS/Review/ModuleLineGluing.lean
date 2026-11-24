/-
Copyright 2026 Axel Delaval, Jie Xu, Shitan Xu, and H5/NOS Lane6 contributors.
Released under the Apache License, Version 2.0.

NOTICE OF MODIFICATION (2026-11-14): new strong local-ISO realization wrapper
around the ACTUAL W07 Zariski module-morphism gluing proof at c4254cce. The
source proof, licenses, model/point maps and toolchain are unchanged.

Unlike a mere Nonempty global iso, this result freezes the ACTUAL pullback
of its hom on every local chart. Full faithfulness is DERIVED from the actual
jointly-surjective open-immersion cover, not supplied as an unknown Fact.
This permits diagonal/generic line-isomorphism gluing and checking cocycles
on a real cover. GIVEN modules/local isos remain explicit inputs; no generic
ample-line extension, model existence or effective original-O scheme is claimed.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZariskiDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- Actual module morphisms are determined on an ACTUAL open-immersion cover. -/
theorem module_hom_ext_openCover {X : Scheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} (u : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (u i)]
    (hu : ⨆ i, (u i).opensRange = ⊤)
    {M N : modulesPseudofunctor.obj (.mk (op X))} {a b : M ⟶ N}
    (hab : ∀ i, (modulesPseudofunctor.map (u i).op.toLoc).toFunctor.map a =
      (modulesPseudofunctor.map (u i).op.toLoc).toFunctor.map b) : a = b := by
  apply (bijective_toDescentData_map_of_isOpenImmersion u hu M N).1
  exact Pseudofunctor.DescentData.hom_ext hab

/-- Glue compatible ACTUAL local isomorphisms, returning the actual global
iso AND its original-chart hom equations. No descent effectiveness premise. -/
theorem exists_iso_of_openCover_compatible
    {X : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
    (u : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (u i)]
    (hu : ⨆ i, (u i).opensRange = ⊤)
    (M N : modulesPseudofunctor.obj (.mk (op X)))
    (e : ∀ i, (modulesPseudofunctor.map (u i).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map (u i).op.toLoc).toFunctor.obj N)
    (hc : ∀ {T : Scheme.{u}} (q : T ⟶ X) (i j : I)
      (a : T ⟶ U i) (b : T ⟶ U j) (ha : a ≫ u i = q) (hb : b ≫ u j = q),
      pullHom (e i).hom a q q ha ha = pullHom (e j).hom b q q hb hb) :
    ∃ E : M ≅ N, ∀ i,
      (modulesPseudofunctor.map (u i).op.toLoc).toFunctor.map E.hom = (e i).hom := by
  let F := modulesPseudofunctor.toDescentData u
  let d : F.obj M ≅ F.obj N := DescentData.isoMk e (fun T q i j a b ha hb => by
    erw [DescentData.ofObj_hom, DescentData.ofObj_hom]
    erw [map_eq_pullHom (e i).hom a q q ha ha,
      map_eq_pullHom (e j).hom b q q hb hb]
    rw [hc q i j a b ha hb]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc])
  have hf (P Q : modulesPseudofunctor.obj (.mk (op X))) :=
    bijective_toDescentData_map_of_isOpenImmersion u hu P Q
  obtain ⟨a, ha⟩ := (hf M N).2 d.hom
  obtain ⟨b, hb⟩ := (hf N M).2 d.inv
  let E : M ≅ N :=
    { hom := a
      inv := b
      hom_inv_id := (hf M M).1 (by
        rw [CategoryTheory.Functor.map_comp, ha, hb, d.hom_inv_id]
        exact (CategoryTheory.Functor.map_id F M).symm)
      inv_hom_id := (hf N N).1 (by
        rw [CategoryTheory.Functor.map_comp, ha, hb, d.inv_hom_id]
        exact (CategoryTheory.Functor.map_id F N).symm) }
  refine ⟨E, fun i => ?_⟩
  exact congrArg (fun f : F.obj M ⟶ F.obj N => f.hom i) ha

#print axioms module_hom_ext_openCover
#print axioms exists_iso_of_openCover_compatible

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
