import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual adjunction mate composition and native module-pullback units

L6-owned categorical coherence for the native W07 H-pullback assembly.
The module unit equations refer to the EXISTING native pullbackComp /
pullbackId, not a replacement isomorphism or a supplied geometric model.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace ZInQ.Contrib.CloudR2Poincare.L6

section TwoCategories

variable {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}

/-- The ACTUAL hom-set equivalences commute with a natural transformation and its mate. -/
theorem homEquiv_conjugate_precomp
    (adj : F ⊣ G) (adj' : F' ⊣ G') (α : F' ⟶ F)
    {X : C} {Y : D} (h : F.obj X ⟶ Y) :
    adj'.homEquiv X Y (α.app X ≫ h) =
      adj.homEquiv X Y h ≫ (conjugateEquiv adj adj' α).app Y := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← unit_conjugateEquiv adj adj' α X,
    Category.assoc, ← (conjugateEquiv adj adj' α).naturality h]
  rw [Category.assoc]

end TwoCategories

section ThreeCategories

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F₁ : C ⥤ D} {R₁ : D ⥤ C} {F₂ : D ⥤ E} {R₂ : E ⥤ D}
    {F : C ⥤ E} {R : E ⥤ C}

private theorem default_leftCompIso_conjugate
    (adj₁ : F₁ ⊣ R₁) (adj₂ : F₂ ⊣ R₂) (adj : F ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) :
    conjugateEquiv adj (adj₁.comp adj₂)
      (Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).hom = e.inv := by
  change (conjugateEquiv adj (adj₁.comp adj₂))
    ((conjugateEquiv adj (adj₁.comp adj₂)).symm e.inv) = e.inv
  exact Equiv.apply_symm_apply _ _

private theorem default_compAdjunct_homEquiv
    (adj₁ : F₁ ⊣ R₁) (adj₂ : F₂ ⊣ R₂)
    {X : C} {Y : D} {Z : E} (a : X ⟶ R₁.obj Y) (b : Y ⟶ R₂.obj Z) :
    (adj₁.comp adj₂).homEquiv X Z
      (F₂.map ((adj₁.homEquiv X Y).symm a) ≫ (adj₂.homEquiv Y Z).symm b) =
      a ≫ R₁.map b := by
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply,
    CategoryTheory.Functor.comp_obj, Category.comp_id]
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

private theorem default_leftCompAdjunct_homEquiv
    (adj₁ : F₁ ⊣ R₁) (adj₂ : F₂ ⊣ R₂) (adj : F ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) {X : C} {Z : E} (c : X ⟶ (R₂ ⋙ R₁).obj Z) :
    (adj₁.comp adj₂).homEquiv X Z
      ((Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).hom.app X ≫
        (adj.homEquiv X Z).symm (c ≫ e.hom.app Z)) = c := by
  rw [homEquiv_conjugate_precomp adj (adj₁.comp adj₂),
    default_leftCompIso_conjugate adj₁ adj₂ adj e, Equiv.apply_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Composition of ACTUAL adjunct coefficient arrows through the canonical left-composition iso. -/
theorem adjunct_comp_leftCompIso
    (adj₁ : F₁ ⊣ R₁) (adj₂ : F₂ ⊣ R₂) (adj : F ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) {X : C} {Y : D} {Z : E}
    (a : X ⟶ R₁.obj Y) (b : Y ⟶ R₂.obj Z) :
    F₂.map ((adj₁.homEquiv X Y).symm a) ≫ (adj₂.homEquiv Y Z).symm b =
      (Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).hom.app X ≫
        (adj.homEquiv X Z).symm (a ≫ R₁.map b ≫ e.hom.app Z) := by
  apply ((adj₁.comp adj₂).homEquiv X Z).injective
  simpa only [Category.assoc] using
    (default_compAdjunct_homEquiv adj₁ adj₂ a b).trans
      (default_leftCompAdjunct_homEquiv adj₁ adj₂ adj e (a ≫ R₁.map b)).symm

end ThreeCategories

section NativeModules

universe u
open AlgebraicGeometry

/-- Composition of the actual module pullback units is the actual composite-morphism unit,
when followed by the EXISTING pullbackComp coefficient isomorphism. -/
theorem nativePullbackComp_unit
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M ≫
        (Scheme.Modules.pushforward b).map
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
            ((Scheme.Modules.pullback b).obj M)) ≫
        (Scheme.Modules.pushforwardComp a b).hom.app
          ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M)) ≫
        (Scheme.Modules.pushforward (a ≫ b)).map
          ((Scheme.Modules.pullbackComp a b).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).unit.app M := by
  let adjC := (Scheme.Modules.pullbackPushforwardAdjunction b).comp
    (Scheme.Modules.pullbackPushforwardAdjunction a)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)
  have h := unit_conjugateEquiv adjC adj (Scheme.Modules.pullbackComp a b).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg
    (fun f => f ≫ (Scheme.Modules.pushforward (a ≫ b)).map
      ((Scheme.Modules.pullbackComp a b).hom.app M)) h
  have hm : (Scheme.Modules.pushforward (a ≫ b)).map
      ((Scheme.Modules.pullbackComp a b).inv.app M) ≫
        (Scheme.Modules.pushforward (a ≫ b)).map
          ((Scheme.Modules.pullbackComp a b).hom.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
  simp only [Category.assoc] at h'
  rw [hm] at h'
  have h'' := h'.trans (CategoryTheory.Category.comp_id (adj.unit.app M))
  simpa only [adj, adjC, Adjunction.comp_unit_app, Category.assoc,
    CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] using h''

/-- The actual identity module-pullback unit becomes the identity-pushforward coefficient. -/
theorem nativePullbackId_unit (X : Scheme.{u}) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
        (Scheme.Modules.pushforward (𝟙 X)).map
          ((Scheme.Modules.pullbackId X).hom.app M) =
      (Scheme.Modules.pushforwardId X).inv.app M := by
  have h := unit_conjugateEquiv (Adjunction.id (C := X.Modules))
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  simpa only [Adjunction.id, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.id_obj] using h.symm

end NativeModules

end ZInQ.Contrib.CloudR2Poincare.L6
