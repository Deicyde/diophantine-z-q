/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Generic PF-carrier native comparison isos. Native five-factor values and
PF pullHom equations are matched BEFORE specialization to original G. No
line cocycle or ampleness assumption and no kernel budget changes.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeCoherence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- Literal native five factors with PF coefficient objects explicit. -/
def nativeDirectLineIso {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (t : Z ⟶ Y) (x y : Z ⟶ X) (hx : t ≫ f₁ = x) (hy : t ≫ f₂ = y) :
    (modulesPseudofunctor.map x.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map y.op.toLoc).toFunctor.obj M :=
  ((Scheme.Modules.pullbackCongr hx).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp t f₁).app M).symm ≪≫
    (Scheme.Modules.pullback t).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp t f₂).app M) ≪≫
    ((Scheme.Modules.pullbackCongr hy).app M)

/-- Opaque generic hom projection, with the SAME PF carrier on both sides. -/
theorem nativeDirectLineIso_hom {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (t : Z ⟶ Y) (x y : Z ⟶ X) (hx : t ≫ f₁ = x) (hy : t ≫ f₂ = y) :
    (nativeDirectLineIso M f₁ f₂ ψ t x y hx hy).hom =
      pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
        (f₁ := f₁) (f₂ := f₂) ψ.hom t x y hx hy := by
  simpa only [nativeDirectLineIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] using
      (native_pullHom_explicit ψ.hom t x y hx hy).symm

/-- Generic four factors for the 23 chart, keeping its original target equality. -/
def nativeSecondLineIso {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (t : Z ⟶ Y) (z : Z ⟶ X) (hz : z = t ≫ f₂) :
    (modulesPseudofunctor.map (t ≫ f₁).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map z.op.toLoc).toFunctor.obj M :=
  ((Scheme.Modules.pullbackComp t f₁).app M).symm ≪≫
    (Scheme.Modules.pullback t).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp t f₂).app M) ≪≫
    ((Scheme.Modules.pullbackCongr hz).app M).symm

theorem nativeSecondLineIso_hom {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (t : Z ⟶ Y) (z : Z ⟶ X) (hz : z = t ≫ f₂) :
    (nativeSecondLineIso M f₁ f₂ ψ t z hz).hom =
      pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
        (f₁ := f₁) (f₂ := f₂) ψ.hom t (t ≫ f₁) z rfl hz.symm := by
  subst z
  simpa only [nativeSecondLineIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    native_pullbackCongr_self_inv_nat, native_pullbackCongr_self_inv,
    Category.comp_id] using (modulesPseudofunctor_pullHom_eq ψ.hom t).symm

#print axioms nativeDirectLineIso_hom
#print axioms nativeSecondLineIso_hom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
