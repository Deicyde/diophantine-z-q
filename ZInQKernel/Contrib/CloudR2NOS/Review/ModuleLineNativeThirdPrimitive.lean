/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Generic PF-carrier native three-factor comparison, with opaque hom projection.
No scheme-specific unfolding, cocycle assumption or kernel budget change.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeChartPrimitive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

def nativeThirdLineIso {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (t : Z ⟶ Y) :
    (modulesPseudofunctor.map (t ≫ f₁).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map (t ≫ f₂).op.toLoc).toFunctor.obj M :=
  ((Scheme.Modules.pullbackComp t f₁).app M).symm ≪≫
    (Scheme.Modules.pullback t).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp t f₂).app M)

theorem nativeThirdLineIso_hom {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (t : Z ⟶ Y) :
    (nativeThirdLineIso M f₁ f₂ ψ t).hom =
      pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
        (f₁ := f₁) (f₂ := f₂) ψ.hom t (t ≫ f₁) (t ≫ f₂) rfl rfl := by
  simpa only [nativeThirdLineIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] using
      (modulesPseudofunctor_pullHom_eq ψ.hom t).symm

#print axioms nativeThirdLineIso_hom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
