import Mathlib.CategoryTheory.Functor.Flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (E : Type u₃) [Category.{v₃} E] (F : C ⥤ D)
variable [∀ (X : D), HasColimitsOfShape (CostructuredArrow F X) E]

/-- The pointwise evaluation of the genuine left Kan extension, without
requiring the object and hom universes of the sites to agree. -/
noncomputable def lanEvaluationMixedIso (X : D) :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim := by
  symm
  refine NatIso.ofComponents (fun G => (F.leftKanExtensionObjIsoColimit G X).symm) ?_
  intro G H f
  apply colimit.hom_ext
  intro T
  let P := CostructuredArrow.proj F X
  let K : (C ⥤ E) ⥤ (D ⥤ E) := F.lan
  change colimit.ι (P ⋙ G) T ≫
      (colim.map (Functor.whiskerLeft P f) ≫ (F.leftKanExtensionObjIsoColimit H X).inv) =
    colimit.ι (P ⋙ G) T ≫ ((F.leftKanExtensionObjIsoColimit G X).inv ≫ (K.map f).app X)
  have hf : colimit.ι (P ⋙ G) T ≫ colim.map (Functor.whiskerLeft P f) =
      f.app T.left ≫ colimit.ι (P ⋙ H) T := ι_colimMap _ _
  have hu : f.app T.left ≫ (F.leftKanExtensionUnit H).app T.left =
      (F.leftKanExtensionUnit G).app T.left ≫ (K.map f).app (F.obj T.left) :=
    congr_app ((F.lanUnit (H := E)).naturality f) T.left
  have hn : (K.obj G).map T.hom ≫ (K.map f).app X =
      (K.map f).app (F.obj T.left) ≫ (K.obj H).map T.hom := (K.map f).naturality T.hom
  have hG : colimit.ι (P ⋙ G) T ≫ (F.leftKanExtensionObjIsoColimit G X).inv =
      (F.leftKanExtensionUnit G).app T.left ≫ (K.obj G).map T.hom :=
    F.ι_leftKanExtensionObjIsoColimit_inv G X T
  have hH : colimit.ι (P ⋙ H) T ≫ (F.leftKanExtensionObjIsoColimit H X).inv =
      (F.leftKanExtensionUnit H).app T.left ≫ (K.obj H).map T.hom :=
    F.ι_leftKanExtensionObjIsoColimit_inv H X T
  have h₀ : colimit.ι (P ⋙ G) T ≫
      (colim.map (Functor.whiskerLeft P f) ≫ (F.leftKanExtensionObjIsoColimit H X).inv) =
      f.app T.left ≫ ((F.leftKanExtensionUnit H).app T.left ≫ (K.obj H).map T.hom) := by
    rw [← Category.assoc, hf, Category.assoc, hH]
    rfl
  have h₁ : f.app T.left ≫ ((F.leftKanExtensionUnit H).app T.left ≫ (K.obj H).map T.hom) =
      (F.leftKanExtensionUnit G).app T.left ≫ ((K.obj G).map T.hom ≫ (K.map f).app X) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : G.obj T.left ⟶ (K.obj H).obj (F.obj T.left) =>
        k ≫ (K.obj H).map T.hom) hu).trans
      ((Category.assoc _ _ _).trans
      (congrArg (fun k : (K.obj G).obj (F.obj T.left) ⟶ (K.obj H).obj X =>
        (F.leftKanExtensionUnit G).app T.left ≫ k) hn.symm)))
  have h₂ : colimit.ι (P ⋙ G) T ≫ ((F.leftKanExtensionObjIsoColimit G X).inv ≫ (K.map f).app X) =
      (F.leftKanExtensionUnit G).app T.left ≫ ((K.obj G).map T.hom ≫ (K.map f).app X) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : G.obj T.left ⟶ (K.obj G).obj X => k ≫ (K.map f).app X) hG).trans
        (Category.assoc _ _ _))
  exact h₀.trans (h₁.trans h₂.symm)

end RC53.EllAdic
