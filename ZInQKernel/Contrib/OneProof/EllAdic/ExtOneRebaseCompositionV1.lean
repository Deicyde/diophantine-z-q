import ZInQKernel.Contrib.OneProof.EllAdic.ExtOneRebaseTransportV1

set_option autoImplicit false

/-! The degree-one endpoint transport for exact additive functors. -/

namespace RC53.EllAdic

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe wC wD wE

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasExt.{wC} C] [HasExt.{wD} D] [HasExt.{wE} E]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem extOneTransport_apply {X Y : C} {U V : D}
    (s : U ⟶ F.obj X) (t : F.obj Y ⟶ V) (y : Ext.{wC} X Y 1) :
    extOneTransport F s t y =
      ((Ext.mk₀ s).comp (y.mapExactFunctor F) (zero_add 1)).comp (Ext.mk₀ t) (add_zero 1) :=
  rfl

section Composition

variable (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem extOneTransport_comp {X Y : C} {U V : D} {P Q : E}
    (s : U ⟶ F.obj X) (t : F.obj Y ⟶ V)
    (s' : P ⟶ G.obj U) (t' : G.obj V ⟶ Q) :
    (extOneTransport G s' t').comp (extOneTransport F s t) =
      extOneTransport (F ⋙ G) (s' ≫ G.map s) (G.map t ≫ t') := by
  apply AddMonoidHom.ext
  intro y
  simp only [AddMonoidHom.comp_apply, extOneTransport_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_mapExactFunctor, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc]

end Composition

/-- The same source and target objects can compare two routes if their endpoint arrows
intertwine the components of the chosen natural isomorphism. -/
theorem extOneTransport_naturality {G : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (θ : F ≅ G)
    {X Y : C} {U V : D} {sF : U ⟶ F.obj X} {sG : U ⟶ G.obj X}
    {tF : F.obj Y ⟶ V} {tG : G.obj Y ⟶ V}
    (hs : sF ≫ θ.hom.app X = sG) (ht : tF = θ.hom.app Y ≫ tG)
    (y : Ext.{wC} X Y 1) :
    extOneTransport F sF tF y = extOneTransport G sG tG y := by
  simp only [extOneTransport_apply]
  rw [ht, ← Ext.mk₀_comp_mk₀ (θ.hom.app Y) tG,
    ← Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ sF) (y.mapExactFunctor F)
      (Ext.mk₀ (θ.hom.app Y)) (zero_add 1),
    Ext.mapExactFunctor_comp_mk₀_natTransApp y θ.hom,
    Ext.mk₀_comp_mk₀_assoc, hs]

end RC53.EllAdic
