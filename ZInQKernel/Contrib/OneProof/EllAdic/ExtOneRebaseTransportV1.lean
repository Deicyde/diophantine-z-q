import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

set_option autoImplicit false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace RC53.EllAdic

universe w w' v u v' u'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [HasExt.{w} C] [HasExt.{w'} D]

/-- Apply the actual Ext functor map and its specified source and target
transports. This is the operation used on degree-one cohomology under a
geometric site equivalence. -/
noncomputable def extOneTransport (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {X Y : C} {U V : D}
    (s : U ⟶ F.obj X) (t : F.obj Y ⟶ V) : Ext.{w} X Y 1 →+ Ext.{w'} U V 1 :=
  ((Ext.mk₀ t).postcomp U (add_zero 1)).comp
    (((Ext.mk₀ s).precomp (F.obj Y) (zero_add 1)).comp (F.mapExtAddHom X Y 1))

/-- This is the literal reduction/projection square after applying Ext.
The only premise is the square of coefficient sheaf maps. -/
theorem extOneTransport_postcomp (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y Y' : C} {U V V' : D} (s : U ⟶ F.obj X)
    (t : F.obj Y ⟶ V) (t' : F.obj Y' ⟶ V') (d : Y ⟶ Y') (b : V ⟶ V')
    (h : F.map d ≫ t' = t ≫ b) (x : Ext.{w} X Y 1) :
    (extOneTransport F s t x).comp (Ext.mk₀ b) (add_zero 1) =
      extOneTransport F s t' (x.comp (Ext.mk₀ d) (add_zero 1)) := by
  let α := (Ext.mk₀ s : Ext.{w'} U (F.obj X) 0)
  let y := x.mapExactFunctor F
  have hy : (x.comp (Ext.mk₀ d) (add_zero 1)).mapExactFunctor F =
      y.comp (Ext.mk₀ (F.map d)) (add_zero 1) :=
    (Ext.mapExactFunctor_comp F x (Ext.mk₀ d) (add_zero 1)).trans
      (congrArg (fun z => y.comp z (add_zero 1)) (Ext.mapExactFunctor_mk₀ F d))
  change ((α.comp y (zero_add 1)).comp (Ext.mk₀ t) (add_zero 1)).comp (Ext.mk₀ b) (add_zero 1) =
    (α.comp ((x.comp (Ext.mk₀ d) (add_zero 1)).mapExactFunctor F) (zero_add 1)).comp
      (Ext.mk₀ t') (add_zero 1)
  rw [hy, ← Ext.comp_assoc_of_third_deg_zero α y (Ext.mk₀ (F.map d)) (zero_add 1)]
  rw [Ext.comp_assoc_of_third_deg_zero (α.comp y (zero_add 1)) (Ext.mk₀ t) (Ext.mk₀ b) (add_zero 1),
    Ext.mk₀_comp_mk₀ t b,
    Ext.comp_assoc_of_third_deg_zero (α.comp y (zero_add 1)) (Ext.mk₀ (F.map d)) (Ext.mk₀ t') (add_zero 1),
    Ext.mk₀_comp_mk₀ (F.map d) t', h]

/-- The two degree-one maps agree when the natural transformation of exact
functors has the two specified endpoint squares. Thus checking geometric
naturality amounts to checking ordinary maps of sheaves, not comparing two
abstract equivalences of Ext groups. -/
theorem extOneTransport_of_natTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (θ : F ⟶ G) {X Y : C} {U V : D}
    (s : U ⟶ F.obj X) (t : F.obj Y ⟶ V) (s' : U ⟶ G.obj X) (t' : G.obj Y ⟶ V)
    (hs : s ≫ θ.app X = s') (ht : t = θ.app Y ≫ t') (x : Ext.{w} X Y 1) :
    extOneTransport F s t x = extOneTransport G s' t' x := by
  let a := (Ext.mk₀ s : Ext.{w'} U (F.obj X) 0)
  let b := (Ext.mk₀ (θ.app X) : Ext.{w'} (F.obj X) (G.obj X) 0)
  let c := (Ext.mk₀ (θ.app Y) : Ext.{w'} (F.obj Y) (G.obj Y) 0)
  let d := (Ext.mk₀ t' : Ext.{w'} (G.obj Y) V 0)
  let f := x.mapExactFunctor F
  let g := x.mapExactFunctor G
  have hθ : f.comp c (add_zero 1) = b.comp g (zero_add 1) :=
    Ext.mapExactFunctor_comp_mk₀_natTransApp x θ
  have h0 : (Ext.mk₀ t : Ext.{w'} (F.obj Y) V 0) = c.comp d (add_zero 0) := by
    rw [ht, Ext.mk₀_comp_mk₀]
  have h1 : a.comp b (add_zero 0) = (Ext.mk₀ s' : Ext.{w'} U (G.obj X) 0) := by
    rw [Ext.mk₀_comp_mk₀, hs]
  change (a.comp f (zero_add 1)).comp (Ext.mk₀ t) (add_zero 1) =
    ((Ext.mk₀ s').comp g (zero_add 1)).comp d (add_zero 1)
  calc
    _ = ((a.comp f (zero_add 1)).comp c (add_zero 1)).comp d (add_zero 1) := by
      rw [h0, Ext.comp_assoc_of_third_deg_zero (a.comp f (zero_add 1)) c d (add_zero 1)]
    _ = (a.comp (f.comp c (add_zero 1)) (zero_add 1)).comp d (add_zero 1) := by
      rw [Ext.comp_assoc_of_third_deg_zero a f c (zero_add 1)]
    _ = (a.comp (b.comp g (zero_add 1)) (zero_add 1)).comp d (add_zero 1) := by rw [hθ]
    _ = ((a.comp b (add_zero 0)).comp g (zero_add 1)).comp d (add_zero 1) := by
      rw [Ext.comp_assoc_of_second_deg_zero a b g (zero_add 1)]
    _ = _ := by rw [h1]

end RC53.EllAdic
