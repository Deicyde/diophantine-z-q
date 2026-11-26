import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Yoneda

set_option autoImplicit false

open CategoryTheory

namespace RC53.EllAdic

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  {U : C' ⥤ C} {V : D' ⥤ D}

/-- Take the mate of the *inverse* of the displayed square of right images.
This construction does not choose objectwise isomorphisms. -/
def rebaseMateHom (a : L ⊣ R) (b : L' ⊣ R') (β : V ⋙ R ≅ R' ⋙ U) :
    U ⋙ L ⟶ L' ⋙ V := (mateEquiv b a).symm β.inv

/-- The transpose formula specifying the mate on a literal morphism. -/
theorem rebaseMateHom_transpose (a : L ⊣ R) (b : L' ⊣ R') (β : V ⋙ R ≅ R' ⋙ U)
    {X : C'} {Y : D'} (f : L'.obj X ⟶ Y) :
    a.homEquiv (U.obj X) (V.obj Y) ((rebaseMateHom a b β).app X ≫ V.map f) =
      U.map (b.homEquiv X Y f) ≫ β.inv.app Y := by
  have hunit : a.homEquiv (U.obj X) (V.obj (L'.obj X)) ((rebaseMateHom a b β).app X) =
      U.map (b.unit.app X) ≫ β.inv.app (L'.obj X) := by
    rw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm b a β.inv X).symm
  have hβ : U.map (R'.map f) ≫ β.inv.app Y =
      β.inv.app (L'.obj X) ≫ R.map (V.map f) := β.inv.naturality f
  rw [a.homEquiv_naturality_right]
  change a.homEquiv (U.obj X) (V.obj (L'.obj X)) ((rebaseMateHom a b β).app X) ≫
    R.map (V.map f) = U.map (b.homEquiv X Y f) ≫ β.inv.app Y
  rw [hunit, Category.assoc, ← hβ, ← Category.assoc,
    ← U.map_comp, Adjunction.homEquiv_unit]

private theorem rebaseMate_precomp_obj_bijective (a : L ⊣ R) (b : L' ⊣ R')
    (β : V ⋙ R ≅ R' ⋙ U) [U.Full] [U.Faithful] [V.Full] [V.Faithful] (X : C') (Y : D') :
    Function.Bijective (fun g : V.obj (L'.obj X) ⟶ V.obj Y => (rebaseMateHom a b β).app X ≫ g) := by
  constructor
  · intro g₁ g₂ hh
    obtain ⟨f₁, rfl⟩ := V.map_surjective g₁
    obtain ⟨f₂, rfl⟩ := V.map_surjective g₂
    have ht := congrArg (a.homEquiv (U.obj X) (V.obj Y)) hh
    rw [rebaseMateHom_transpose, rebaseMateHom_transpose] at ht
    have hu := (cancel_mono (β.inv.app Y)).1 ht
    exact congrArg (fun f => V.map f) ((b.homEquiv X Y).injective (U.map_injective hu))
  · intro g
    obtain ⟨h, hh⟩ := U.map_surjective (a.homEquiv (U.obj X) (V.obj Y) g ≫ β.hom.app Y)
    let f := (b.homEquiv X Y).symm h
    refine ⟨V.map f, (a.homEquiv (U.obj X) (V.obj Y)).injective ?_⟩
    rw [rebaseMateHom_transpose]
    change U.map (b.homEquiv X Y ((b.homEquiv X Y).symm h)) ≫ β.inv.app Y = _
    rw [Equiv.apply_symm_apply, hh, Category.assoc]
    have hi : β.hom.app Y ≫ β.inv.app Y = 𝟙 _ := (β.app Y).hom_inv_id
    rw [hi]
    exact Category.comp_id _

private theorem rebaseMateHom_app_isIso (a : L ⊣ R) (b : L' ⊣ R') (β : V ⋙ R ≅ R' ⋙ U)
    [U.Full] [U.Faithful] [V.Full] [V.Faithful] [V.EssSurj] (X : C') :
    IsIso ((rebaseMateHom a b β).app X) := by
  apply isIso_of_coyoneda_map_bijective
  intro Z
  let Y := V.objPreimage Z
  let e : V.obj Y ≅ Z := V.objObjPreimageIso Z
  let k := (rebaseMateHom a b β).app X
  have hk := rebaseMate_precomp_obj_bijective a b β X Y
  constructor
  · intro f g h
    apply (cancel_mono e.inv).1
    apply hk.1
    change k ≫ (f ≫ e.inv) = k ≫ (g ≫ e.inv)
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun z => z ≫ e.inv) h
  · intro f
    obtain ⟨g, hg⟩ := hk.2 (f ≫ e.inv)
    change k ≫ g = f ≫ e.inv at hg
    refine ⟨g ≫ e.hom, ?_⟩
    change k ≫ (g ≫ e.hom) = f
    rw [← Category.assoc, hg, Category.assoc, e.inv_hom_id]
    exact Category.comp_id _

/-- The normalized mate is invertible for the geometric restriction equivalences.
Full faithfulness is used on their literal morphisms and essential surjectivity
only on the pro-étale side. -/
noncomputable def rebaseMateIso (a : L ⊣ R) (b : L' ⊣ R') (β : V ⋙ R ≅ R' ⋙ U)
    [U.Full] [U.Faithful] [V.Full] [V.Faithful] [V.EssSurj] : U ⋙ L ≅ L' ⋙ V :=
  NatIso.ofComponents (fun X =>
    letI : IsIso ((rebaseMateHom a b β).app X) := rebaseMateHom_app_isIso a b β X
    asIso ((rebaseMateHom a b β).app X)) (fun f => (rebaseMateHom a b β).naturality f)

/-- The iso keeps exactly the normalized hom, so the transpose rule applies
without additional comparison premises. -/
theorem rebaseMateIso_hom (a : L ⊣ R) (b : L' ⊣ R') (β : V ⋙ R ≅ R' ⋙ U)
    [U.Full] [U.Faithful] [V.Full] [V.Faithful] [V.EssSurj] :
    (rebaseMateIso a b β).hom = rebaseMateHom a b β := by
  ext X
  rfl

end RC53.EllAdic
