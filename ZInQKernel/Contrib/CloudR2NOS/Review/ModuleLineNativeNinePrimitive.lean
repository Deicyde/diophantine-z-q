/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Generic PF-carrier nine native factors, regrouped BEFORE original-G
specialization. Uses opaque generic native 5/4 hom projections and ordinary
category block composition. No global cocycle/VA/NOS premise or budget change.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeChartPrimitive
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractIsoBlocks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

variable {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
  (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
  (c₁₂ c₁₃ c₂₃ : Z ⟶ Y)
  (h₁ : c₁₂ ≫ f₁ = c₁₃ ≫ f₁) (h₂ : c₁₂ ≫ f₂ = c₂₃ ≫ f₁) (h₃ : c₁₃ ≫ f₂ = c₂₃ ≫ f₂)

def nativeNineLineIso :
    (modulesPseudofunctor.map (c₁₃ ≫ f₁).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map (c₁₃ ≫ f₂).op.toLoc).toFunctor.obj M :=
  ((Scheme.Modules.pullbackCongr h₁).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp c₁₂ f₁).app M).symm ≪≫
    (Scheme.Modules.pullback c₁₂).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp c₁₂ f₂).app M) ≪≫
    ((Scheme.Modules.pullbackCongr h₂).app M) ≪≫
    ((Scheme.Modules.pullbackComp c₂₃ f₁).app M).symm ≪≫
    (Scheme.Modules.pullback c₂₃).mapIso ψ ≪≫
    ((Scheme.Modules.pullbackComp c₂₃ f₂).app M) ≪≫
    ((Scheme.Modules.pullbackCongr h₃).app M).symm

theorem nativeNineLineIso_blocks : nativeNineLineIso M f₁ f₂ ψ c₁₂ c₁₃ c₂₃ h₁ h₂ h₃ =
    nativeDirectLineIso M f₁ f₂ ψ c₁₂ (c₁₃ ≫ f₁) (c₂₃ ≫ f₁) h₁ h₂ ≪≫
      nativeSecondLineIso M f₁ f₂ ψ c₂₃ (c₁₃ ≫ f₂) h₃ := by
  simp only [nativeNineLineIso, nativeDirectLineIso, nativeSecondLineIso, Iso.trans_assoc]

theorem nativeNineLineIso_hom :
    (nativeNineLineIso M f₁ f₂ ψ c₁₂ c₁₃ c₂₃ h₁ h₂ h₃).hom =
      pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M) (f₁ := f₁) (f₂ := f₂)
          ψ.hom c₁₂ (c₁₃ ≫ f₁) (c₂₃ ≫ f₁) h₁ h₂ ≫
        pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M) (f₁ := f₁) (f₂ := f₂)
          ψ.hom c₂₃ (c₂₃ ≫ f₁) (c₁₃ ≫ f₂) rfl h₃.symm := by
  rw [nativeNineLineIso_blocks]
  exact Abstract.iso_blocks_hom
    (nativeDirectLineIso M f₁ f₂ ψ c₁₂ (c₁₃ ≫ f₁) (c₂₃ ≫ f₁) h₁ h₂)
    (nativeSecondLineIso M f₁ f₂ ψ c₂₃ (c₁₃ ≫ f₂) h₃) _ _
    (nativeDirectLineIso_hom M f₁ f₂ ψ c₁₂ (c₁₃ ≫ f₁) (c₂₃ ≫ f₁) h₁ h₂)
    (nativeSecondLineIso_hom M f₁ f₂ ψ c₂₃ (c₁₃ ≫ f₂) h₃)

#print axioms nativeNineLineIso_blocks
#print axioms nativeNineLineIso_hom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
