/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality

/-!
# Coherence is invariant under equivalences of sites

Let `eqv : C ≌ D` be an equivalence of small sites whose functor and inverse are continuous and
cocontinuous, and let `φ : S ⟶ eqv.functor_* R`, `ψ : R ⟶ eqv.inverse_* S` be morphisms of
sheaves of rings satisfying the compatibilities of
`SheafOfModules.pushforwardPushforwardEquivalence`, so that pushing forward along `φ` is an
equivalence between sheaves of `R`-modules and sheaves of `S`-modules. We show that this
equivalence preserves and reflects coherence.

Coherence quantifies over all slices of the site, so the proof restricts the equivalence to each
slice: over `W : C`, `Over.postEquiv W eqv` together with the restrictions of `φ` and `ψ` gives an
equivalence `SheafOfModules.sliceEquivalence` between sheaves of modules over `R.over (eqv W)` and
over `S.over W`, which carries `M.over (eqv W)` to `(φ_* M).over W`. A morphism from a finite free
sheaf to `(φ_* M).over W` is thus the image of one to `M.over (eqv W)`, whose kernel is of finite
type by coherence of `M`, and finite type is carried along by
`SheafOfModules.isFiniteType_pushforward_of_isLeftAdjoint`.

## Main results

- `SheafOfModules.isCoherent_pushforward_of_equivalence`: `M` coherent implies `φ_* M` coherent.
- `SheafOfModules.isCoherent_of_isCoherent_pushforward_of_equivalence`: the converse.
- `CategoryTheory.Equivalence.isContinuous_overPost`: `Over.post` of the functor of an equivalence
  of sites is continuous for the sliced topologies.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Equivalence

variable {C D : Type*} [Category* C] [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (e : C ≌ D)

/-- `Over.post` of the functor of an equivalence of sites is continuous for the sliced
topologies, provided the inverse is cocontinuous. -/
instance isContinuous_overPost [e.inverse.IsCocontinuous K J] (X : C) :
    (Over.post (X := X) e.functor).IsContinuous (J.over X) (K.over (e.functor.obj X)) := by
  haveI : (Over.postEquiv X e).symm.functor.IsCocontinuous (K.over _) (J.over X) :=
    isCocontinuous_comp _ _ (K.over _) (J.over _)
  exact (Over.postEquiv X e).symm.toAdjunction.isContinuous_of_isCocontinuous _ _

/-- `Over.post` of the inverse of an equivalence of sites is continuous for the sliced
topologies, provided the functor is cocontinuous. -/
instance isContinuous_overPost_inverse [e.functor.IsCocontinuous J K] (Y : D) :
    (Over.post (X := Y) e.inverse).IsContinuous (K.over Y) (J.over (e.inverse.obj Y)) :=
  haveI : e.symm.inverse.IsCocontinuous J K := ‹_›
  e.symm.isContinuous_overPost Y

/-- The functor of `Over.postEquiv X e` is continuous. -/
instance isContinuous_postEquiv_functor [e.inverse.IsCocontinuous K J] (X : C) :
    (Over.postEquiv X e).functor.IsContinuous (J.over X) (K.over (e.functor.obj X)) :=
  e.isContinuous_overPost X

/-- The inverse of `Over.postEquiv X e` is continuous. -/
instance isContinuous_postEquiv_inverse [e.functor.IsCocontinuous J K] (X : C) :
    (Over.postEquiv X e).inverse.IsContinuous (K.over (e.functor.obj X)) (J.over X) :=
  have h₁ := e.isContinuous_overPost_inverse (J := J) (K := K) (e.functor.obj X)
  have h₂ : (Over.map (e.unitIso.inv.app X)).IsContinuous
      (J.over (e.inverse.obj (e.functor.obj X))) (J.over X) :=
    inferInstanceAs ((Over.map (e.unitIso.inv.app X)).IsContinuous
      (J.over ((e.functor ⋙ e.inverse).obj X)) (J.over ((𝟭 C).obj X)))
  @Functor.isContinuous_comp _ _ _ _ _ _ (Over.post e.inverse) (Over.map (e.unitIso.inv.app X))
    (K.over (e.functor.obj X)) (J.over _) (J.over X) h₁ h₂

/-- The functor of `Over.postEquiv X e` is cocontinuous. -/
instance isCocontinuous_postEquiv_functor [e.functor.IsCocontinuous J K] (X : C) :
    (Over.postEquiv X e).functor.IsCocontinuous (J.over X) (K.over (e.functor.obj X)) :=
  inferInstanceAs ((Over.post e.functor).IsCocontinuous _ _)

/-- The inverse of `Over.postEquiv X e` is cocontinuous. -/
instance isCocontinuous_postEquiv_inverse [e.inverse.IsCocontinuous K J] (X : C) :
    (Over.postEquiv X e).inverse.IsCocontinuous (K.over (e.functor.obj X)) (J.over X) := by
  have h₂ : (Over.map (e.unitIso.inv.app X)).IsCocontinuous
      (J.over (e.inverse.obj (e.functor.obj X))) (J.over X) :=
    inferInstanceAs ((Over.map (e.unitIso.inv.app X)).IsCocontinuous
      (J.over ((e.functor ⋙ e.inverse).obj X)) (J.over ((𝟭 C).obj X)))
  exact @isCocontinuous_comp _ _ _ _ _ _ (Over.post e.inverse)
    (Over.map (e.unitIso.inv.app X)) (K.over (e.functor.obj X)) (J.over _) (J.over X) _ h₂

end CategoryTheory.Equivalence

namespace SheafOfModules

variable {C D : Type u} [SmallCategory C] [SmallCategory D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (eqv : C ≌ D)
  [eqv.functor.IsContinuous J K] [eqv.inverse.IsContinuous K J]
  [eqv.functor.IsCocontinuous J K] [eqv.inverse.IsCocontinuous K J]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj)

/-- The restriction of `φ` to the slice over `W`. -/
noncomputable abbrev sliceRingHom (W : C) :
    S.over W ⟶ ((Over.post (X := W) eqv.functor).sheafPushforwardContinuous RingCat.{u}
      (J.over W) (K.over (eqv.functor.obj W))).obj (R.over (eqv.functor.obj W)) :=
  ((Over.forget W).sheafPushforwardContinuous RingCat.{u} (J.over W) J).map φ

/-- The restriction of `ψ` to the slice over `eqv.functor.obj W`. -/
noncomputable abbrev sliceRingHomInv (W : C) :
    R.over (eqv.functor.obj W) ⟶ ((Over.postEquiv W eqv).inverse.sheafPushforwardContinuous
      RingCat.{u} (K.over (eqv.functor.obj W)) (J.over W)).obj (S.over W) :=
  ((Over.forget (eqv.functor.obj W)).sheafPushforwardContinuous RingCat.{u} _ K).map ψ

include H₁ H₂ in
/-- The equivalence between sheaves of modules on the slices over `W` and over
`eqv.functor.obj W`. -/
noncomputable def sliceEquivalence (W : C) :
    SheafOfModules.{u} (R.over (eqv.functor.obj W)) ≌ SheafOfModules.{u} (S.over W) :=
  pushforwardPushforwardEquivalence (Over.postEquiv W eqv) (sliceRingHom eqv φ W)
    (sliceRingHomInv eqv ψ W) (by
      ext Z : 2
      exact NatTrans.congr_app H₁ (Opposite.op Z.unop.left)) (by
      ext Z : 2
      exact NatTrans.congr_app H₂ (Opposite.op Z.unop.left))

omit [eqv.functor.IsCocontinuous J K] [eqv.inverse.IsCocontinuous K J] in
include H₂ in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The first compatibility condition for the reverse equivalence `eqv.symm`. -/
lemma symm_H₁ :
    Functor.whiskerRight (NatTrans.op eqv.symm.counit) S.obj =
      φ.hom ≫ eqv.symm.inverse.op.whiskerLeft ψ.hom := by
  ext X : 2
  have h := NatTrans.congr_app H₂ X
  change φ.hom.app X ≫ ψ.hom.app _ ≫ S.obj.map (eqv.unit.app X.unop).op = 𝟙 _ at h
  change S.obj.map (eqv.unitInv.app X.unop).op = φ.hom.app X ≫ ψ.hom.app _
  have e : S.obj.map (eqv.unit.app X.unop).op ≫ S.obj.map (eqv.unitInv.app X.unop).op =
      𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id,
      CategoryTheory.Functor.map_id]
  have h' := h =≫ S.obj.map (eqv.unitInv.app X.unop).op
  rw [Category.assoc, Category.assoc] at h'
  erw [e] at h'
  erw [Category.comp_id, Category.id_comp] at h'
  exact h'.symm

omit [eqv.functor.IsCocontinuous J K] [eqv.inverse.IsCocontinuous K J] in
include H₁ in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The second compatibility condition for the reverse equivalence `eqv.symm`. -/
lemma symm_H₂ :
    ψ.hom ≫ eqv.symm.functor.op.whiskerLeft φ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.symm.unit) R.obj = 𝟙 R.obj := by
  ext X : 2
  have h := NatTrans.congr_app H₁ X
  change R.obj.map (eqv.counit.app X.unop).op = ψ.hom.app X ≫ φ.hom.app _ at h
  change ψ.hom.app X ≫ φ.hom.app _ ≫ R.obj.map (eqv.counitInv.app X.unop).op = 𝟙 _
  have e : R.obj.map (eqv.counit.app X.unop).op ≫ R.obj.map (eqv.counitInv.app X.unop).op =
      𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id,
      CategoryTheory.Functor.map_id]
  rw [← Category.assoc, ← h]
  exact e

variable [HasPullbacks C] [HasPullbacks D]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : D) (Y : Over X), HasSheafify ((K.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : D) (Y : Over X), ((K.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

include H₁ H₂ in
/-- **Coherence is invariant under an equivalence of sites.** -/
theorem isCoherent_pushforward_of_equivalence [IsIso φ]
    (η : (pushforward φ).obj (unit R) ≅ unit S) (M : SheafOfModules.{u} R) [M.IsCoherent] :
    ((pushforward φ).obj M).IsCoherent where
  isFiniteType := isFiniteType_pushforward_of_isLeftAdjoint eqv.functor φ η
  hasFiniteTypeRelations W := by
    intro I _ χ
    let E := sliceEquivalence eqv φ ψ H₁ H₂ W
    let ηW : unit (S.over W) ≅ E.functor.obj (unit (R.over (eqv.functor.obj W))) :=
      ((overFunctor S W).mapIso η).symm
    let χ₁ : free I ⟶ E.functor.obj (M.over (eqv.functor.obj W)) := χ
    let χ' := E.fullyFaithfulFunctor.preimage ((mapFreeIso E.functor I ηW).inv ≫ χ₁)
    haveI : (kernel χ').IsFiniteType := IsCoherent.hasFiniteTypeRelations M _ χ'
    haveI : IsIso (sliceRingHom eqv φ W) := Functor.map_isIso _ φ
    haveI (X : Over W) : (Over.post (Over.post eqv.functor)).IsContinuous ((J.over W).over X)
        ((K.over (eqv.functor.obj W)).over ((Over.post eqv.functor).obj X)) :=
      (Over.postEquiv W eqv).isContinuous_overPost X
    haveI : (E.functor.obj (kernel χ')).IsFiniteType :=
      isFiniteType_pushforward_of_isLeftAdjoint (Over.post eqv.functor) (sliceRingHom eqv φ W)
        ηW.symm
    have hχ : (mapFreeIso E.functor I ηW).hom ≫ E.functor.map χ' = χ₁ := by
      simp [χ']
    exact IsFiniteType.of_iso ((PreservesKernel.iso E.functor χ') ≪≫
      (kernelIsIsoComp _ _).symm ≪≫ kernelIsoOfEq hχ)

include H₁ H₂ in
/-- **Coherence is reflected by an equivalence of sites**: the converse of
`SheafOfModules.isCoherent_pushforward_of_equivalence`. -/
theorem isCoherent_of_isCoherent_pushforward_of_equivalence [IsIso ψ]
    (η : (pushforward φ).obj (unit R) ≅ unit S) (M : SheafOfModules.{u} R)
    (hM : ((pushforward φ).obj M).IsCoherent) : M.IsCoherent := by
  let E := pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂
  haveI : eqv.symm.functor.IsContinuous K J := ‹eqv.inverse.IsContinuous K J›
  haveI : eqv.symm.inverse.IsContinuous J K := ‹eqv.functor.IsContinuous J K›
  haveI : eqv.symm.functor.IsCocontinuous K J := ‹eqv.inverse.IsCocontinuous K J›
  haveI : eqv.symm.inverse.IsCocontinuous J K := ‹eqv.functor.IsCocontinuous J K›
  haveI : IsIso (C := Sheaf K RingCat.{u}) (X := R)
      (Y := (eqv.symm.functor.sheafPushforwardContinuous RingCat.{u} K J).obj S) ψ :=
    ‹IsIso ψ›
  let η' : (pushforward ψ).obj (unit S) ≅ unit R :=
    (pushforward ψ).mapIso η.symm ≪≫ (E.unitIso.app (unit R)).symm
  haveI : ((pushforward ψ).obj ((pushforward φ).obj M)).IsCoherent :=
    isCoherent_pushforward_of_equivalence eqv.symm ψ φ (symm_H₁ eqv φ ψ H₂)
      (symm_H₂ eqv φ ψ H₁) η' ((pushforward φ).obj M)
  exact IsCoherent.of_iso (M := (pushforward ψ).obj ((pushforward φ).obj M))
    (E.unitIso.app M).symm

end SheafOfModules
