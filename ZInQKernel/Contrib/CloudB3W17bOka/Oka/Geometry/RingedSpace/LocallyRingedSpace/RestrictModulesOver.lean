/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesComp
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Topology.Sheaves.Module

/-!
# Restriction of `𝒪`-modules to an open subspace versus restriction to a slice

For a locally ringed space `Y` and an open `V`, a sheaf of `𝒪_Y`-modules `M` can be restricted to
`V` in two ways: as `M.over V`, a sheaf of modules over `𝒪_Y.over V` on the site `Over V`, and as
the pullback `(Y.restrictModules V).obj M` along the open immersion `Y|_V ⟶ Y`, a sheaf of modules
on the space `V`. Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOver` is an equivalence
between the two categories, and we show that it carries the first restriction to the second
(`AlgebraicGeometry.LocallyRingedSpace.overFunctorCompRestrictOverEquivIso`), by comparing right
adjoints. This is the analogue for locally ringed spaces of Mathlib's
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`.

Consequently coherence of `M` on `V` may be tested on either side
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_over_iff_isCoherent_restrictModules`), and
coherence of `M` is local on `Y` for covers by open subspaces
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules`).

The open `V` is typed `Opens ↑↑Y.toPresheafedSpace`, the spelling of the site of
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf`; with the spelling `Opens ↑Y.toTopCat` the
instances needed by `SheafOfModules.overPushforwardOverAdj` are not found.
-/

open CategoryTheory TopologicalSpace Limits

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u}) (V : Opens Y.toPresheafedSpace)

/-- Sheaves of modules over `𝒪_Y.over V` are equivalent to sheaves of modules on the open
subspace `Y|_V`: Mathlib's `TopologicalSpace.Opens.sheafOfModulesEquivOver`. -/
noncomputable def restrictOverEquiv :
    SheafOfModules.{u} (Y.ringSheaf.over V) ≌
      SheafOfModules.{u} (Y.restrict V.isOpenEmbedding).ringSheaf :=
  V.sheafOfModulesEquivOver Y.ringSheaf

/-- Restricting to `Over V` and then passing to the subspace `V` is left adjoint to going back
along the equivalence and then pushing forward along `Over.star V`. -/
noncomputable def overRestrictAdj :
    SheafOfModules.overFunctor Y.ringSheaf V ⋙ (restrictOverEquiv Y V).functor ⊣
      (restrictOverEquiv Y V).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := Y.ringSheaf) V) :=
  (SheafOfModules.overPushforwardOverAdj V).comp (restrictOverEquiv Y V).toAdjunction

/-- The composite `Opens Y ⥤ Over V ⥤ Opens V`, `U ↦ (U × V ⟶ V) ↦ U ∩ V`, is the preimage
functor of the inclusion `V ⟶ Y`. -/
noncomputable def starOverEquivalenceIso :
    (Over.star V ⋙ V.overEquivalence.symm.inverse) ≅
      (Opens.map (Y.ofRestrict V.isOpenEmbedding).base :
        Opens Y.toPresheafedSpace ⥤ Opens ↥V) :=
  NatIso.ofComponents (fun U => eqToIso (by
    ext x
    change x.1 ∈ ((Over.star V).obj U).left ↔ x.1 ∈ U
    simp)) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoint in `AlgebraicGeometry.LocallyRingedSpace.overRestrictAdj` is the
pushforward of modules along the open immersion `Y|_V ⟶ Y`. -/
noncomputable def restrictOverInverseIso :
    (restrictOverEquiv Y V).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := Y.ringSheaf) V) ≅
      SheafOfModules.pushforward.{u} (Y.ofRestrict V.isOpenEmbedding).toRingSheafHom := by
  haveI : (Over.star V ⋙ V.overEquivalence.symm.inverse).IsContinuous
      (Opens.grothendieckTopology Y.toPresheafedSpace) (Opens.grothendieckTopology ↥V) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology _).over V) _
  haveI : (Opens.map (Y.ofRestrict V.isOpenEmbedding).base :
      Opens Y.toPresheafedSpace ⥤ Opens ↥V).IsContinuous
      (Opens.grothendieckTopology Y.toPresheafedSpace) (Opens.grothendieckTopology ↥V) :=
    inferInstanceAs ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).IsContinuous
      (Opens.grothendieckTopology Y.toPresheafedSpace)
      (Opens.grothendieckTopology (Y.restrict V.isOpenEmbedding).toPresheafedSpace))
  refine (SheafOfModules.pushforwardComp _ _).trans ?_
  refine (SheafOfModules.pushforwardNatIso (J := Opens.grothendieckTopology Y.toPresheafedSpace)
    (K := Opens.grothendieckTopology ↥V) _ (starOverEquivalenceIso Y V).symm).trans ?_
  refine SheafOfModules.pushforwardCongr ?_
  ext U x
  simp only [ringSheaf, SheafOfModules.pushforwardOver, Functor.comp_map,
    Opens.sheafRestrictSheafEquivOver, Opens.overPullbackSheafEquivOver, Iso.app_inv, Iso.symm_inv,
    Iso.isoCompInverse_hom_app, Iso.refl_hom, NatTrans.id_app, Functor.map_comp,
    starOverEquivalenceIso, Iso.symm_hom, Category.assoc, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Opens.sheafEquivOver_unitIso_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_obj_obj_map, Over.forget_obj, Quiver.Hom.unop_op,
    Over.forget_map, Opens.overEquivalence_unitIso_inv_app_left, eqToHom_op,
    Opens.sheafEquivOver_inverse_map_hom_app, ObjectProperty.FullSubcategory.id_hom,
    Functor.whiskerRight_app, NatTrans.op_app, NatIso.ofComponents_inv_app, eqToIso.inv,
    Opens.sheafRestrict_obj_obj_map, eqToHom_unop, RingCat.hom_comp,
    CommRingCat.forgetToRingCat_map_hom, RingHom.coe_comp, Function.comp_apply,
    Hom.toRingSheafHom]
  have key : ∀ {A B C D : (Opens Y.toPresheafedSpace)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
      (k : A ⟶ D) (x : Y.presheaf.obj A),
      Y.presheaf.map h (Y.presheaf.map g (Y.presheaf.map f x)) = Y.presheaf.map k x :=
    fun f g h k x => by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, Subsingleton.elim (f ≫ g ≫ h) k]
  exact key _ _ _ _ x

/-- **Restriction to a slice, read on the open subspace, is restriction to the open subspace**:
`M ↦ M.over V` followed by `TopologicalSpace.Opens.sheafOfModulesEquivOver` is the pullback
along the open immersion `Y|_V ⟶ Y`. Both are left adjoint to the pushforward along it. -/
noncomputable def overFunctorCompRestrictOverEquivIso :
    SheafOfModules.overFunctor Y.ringSheaf V ⋙ (restrictOverEquiv Y V).functor ≅
      Y.restrictModules V :=
  ((overRestrictAdj Y V).ofNatIsoRight (restrictOverInverseIso Y V)).leftAdjointUniq
    (Y.ofRestrict V.isOpenEmbedding).pullbackModulesAdj

/-- The restriction `(Y.restrictModules V).obj M` corresponds to `M.over V` under
`AlgebraicGeometry.LocallyRingedSpace.restrictOverEquiv`. -/
noncomputable def restrictModulesObjIso (M : SheafOfModules.{u} Y.ringSheaf) :
    (Y.restrictModules V).obj M ≅ (restrictOverEquiv Y V).functor.obj (M.over V) :=
  ((overFunctorCompRestrictOverEquivIso Y V).app M).symm

/-- **Coherence on an open subspace may be tested on the slice**: `M.over V` is coherent if and
only if the restriction of `M` to the open subspace `Y|_V` is. -/
theorem isCoherent_over_iff_isCoherent_restrictModules (M : SheafOfModules.{u} Y.ringSheaf) :
    (M.over V).IsCoherent ↔ ((Y.restrictModules V).obj M).IsCoherent := by
  rw [← V.isCoherent_sheafOfModulesEquivOver_functor_obj_iff Y.ringSheaf]
  constructor
  · intro h
    exact SheafOfModules.IsCoherent.of_iso.{u}
      (M := (V.sheafOfModulesEquivOver Y.ringSheaf).functor.obj (M.over V))
      (restrictModulesObjIso Y V M).symm
  · intro h
    exact SheafOfModules.IsCoherent.of_iso.{u} (M := (Y.restrictModules V).obj M)
      (restrictModulesObjIso Y V M)

/-- **Coherence is local on a locally ringed space**: if every point of `Y` has an open
neighbourhood on which the restriction of `M` is coherent, then `M` is coherent. -/
theorem isCoherent_of_isCoherent_restrictModules (M : SheafOfModules.{u} Y.ringSheaf)
    (h : ∀ y : Y, ∃ (V : Opens Y.toPresheafedSpace) (_ : y ∈ V),
      ((Y.restrictModules V).obj M).IsCoherent) :
    M.IsCoherent := by
  choose V hV hcoh using h
  haveI (y : Y) : (M.over (V y)).IsCoherent :=
    (isCoherent_over_iff_isCoherent_restrictModules Y (V y) M).2 (hcoh y)
  refine SheafOfModules.IsCoherent.of_coversTop M V ((Opens.coversTop_iff _ V).2 ?_)
  exact eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hV y⟩

end AlgebraicGeometry.LocallyRingedSpace
