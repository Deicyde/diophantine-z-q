import Mathlib

namespace ZInQ.DefFaltings
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- (copied) -/
structure AbVar (K : Type) [Field K] where
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

/-- (copied) Base change `A_L`. -/
noncomputable def AbVar.baseChange {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L]
    [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

open NumberField

/-- The generic fibre `𝒢_L` of a scheme `𝒢` over `𝓞_L`. -/
noncomputable def genericFibre (L : Type) [Field L] [NumberField L]
    (G : Over (Spec (CommRingCat.of (𝓞 L)))) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj G

structure GroupModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] where
  G : Over (Spec (CommRingCat.of (𝓞 L)))
  [grp : GrpObj G]
  [smooth : Smooth G.hom]
  [separated : IsSeparated G.hom]
  [qc : QuasiCompact G.hom]
  gen : genericFibre L G ≅ (A.baseChange L).X
  gen_hom : letI : GrpObj (genericFibre L G) := Functor.grpObjObj
    IsMonHom gen.hom

attribute [instance] GroupModel.grp GroupModel.smooth GroupModel.separated GroupModel.qc

end ZInQ.DefFaltings

namespace G0StableBC
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.DefFaltings NumberField
open scoped Obj

def BaseChangeCompIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L M : Type) [Field L] [Algebra K L] [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M],
    ∃ e : ((A.baseChange L).baseChange M).X ≅ (A.baseChange M).X, IsMonHom e.hom

/-- `f^* g^* G → (f ≫ g)^* G` (h5-neron). -/
noncomputable def pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj G) ⟶ (Over.pullback (f ≫ g)).obj G :=
  (Over.pullbackComp f g).inv.app G

theorem isMonHom_pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompInv f g G) := by
  have h := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
      (Mon.mk G) ≫ (Functor.mapMonNatIso (Over.pullbackComp f g)).inv.app (Mon.mk G)).isMonHom_hom
  have e : pbCompInv f g G = 𝟙 _ ≫ pbCompInv f g G := (Category.id_comp _).symm
  rw [e]
  exact h

/-- Pullback pasting for group objects, with an arbitrary third side `h = f ≫ g`. -/
theorem exists_pbPaste {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (sq : f ≫ g = h)
    (G : Over Z) [GrpObj G] :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback h).obj G) := Functor.grpObjObj
    ∃ e : (Over.pullback f).obj ((Over.pullback g).obj G) ≅ (Over.pullback h).obj G,
      IsMonHom e.hom := by
  subst sq
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj G)) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (f ≫ g)).obj G) := Functor.grpObjObj
  exact ⟨(Over.pullbackComp f g).symm.app G, isMonHom_pbCompInv f g G⟩

theorem baseChangeCompIso : BaseChangeCompIso := by
  intro K _ A L M _ _ _ _ _ _
  have sq : Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact exists_pbPaste _ _ _ sq A.X

/-- Pasting two pullback squares, with a group-scheme iso on one leg. -/
theorem exists_pbSquare {X Y₁ Y₂ Z : Scheme.{0}} (f₁ : X ⟶ Y₁) (g₁ : Y₁ ⟶ Z) (f₂ : X ⟶ Y₂)
    (g₂ : Y₂ ⟶ Z) (sq : f₁ ≫ g₁ = f₂ ≫ g₂) (G : Over Z) [GrpObj G] (H : Over Y₂) [GrpObj H]
    (u : (Over.pullback g₂).obj G ≅ H)
    (hu : letI : GrpObj ((Over.pullback g₂).obj G) := Functor.grpObjObj; IsMonHom u.hom) :
    letI : GrpObj ((Over.pullback g₁).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f₁).obj ((Over.pullback g₁).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f₂).obj H) := Functor.grpObjObj
    ∃ e : (Over.pullback f₁).obj ((Over.pullback g₁).obj G) ≅ (Over.pullback f₂).obj H,
      IsMonHom e.hom := by
  obtain ⟨e₁, he₁⟩ := exists_pbPaste f₁ g₁ (f₁ ≫ g₁) rfl G
  obtain ⟨e₂, he₂⟩ := exists_pbPaste f₂ g₂ (f₁ ≫ g₁) sq.symm G
  have hu' : IsMonHom ((Over.pullback f₂).map u.hom) := inferInstance
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ (Over.pullback f₂).mapIso u,
    (inferInstance : IsMonHom (e₁.hom ≫ e₂.inv ≫ (Over.pullback f₂).map u.hom))⟩

section H5
variable {K : Type} [Field K] {A : AbVar K}
def IsBaseChangeOf {L L' : Type} [Field L] [NumberField L] [Algebra K L] [Field L']
    [NumberField L'] [Algebra K L'] [Algebra L L'] (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) :
    Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom
end H5

def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

theorem square1 (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] :
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))) =
      Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  obtain ⟨c, hc⟩ := baseChangeCompIso K A L L'
  obtain ⟨e, he⟩ := exists_pbSquare _ _ _ _ (square1 L L') 𝒢.G (A.baseChange L).X 𝒢.gen 𝒢.gen_hom
  refine ⟨⟨_, e ≪≫ c, ?_⟩, Iso.refl _, ?_⟩
  · exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ e.hom c.hom he hc
  · exact (inferInstance : IsMonHom (𝟙 ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G)))

end G0StableBC

#print axioms G0StableBC.baseChangeCompIso
#print axioms G0StableBC.groupModelBaseChangeExists
