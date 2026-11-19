/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

GENERIC native nine-factor conversion from an ACTUAL 5/4 block iso equality.
The regrouping is proved in the common PF category before concrete scheme
maps are substituted. This conditional primitive is not a new cocycle input
of NOS: the original-G endpoint supplies its already-proved block equality.
No frozen source, universe, axiom or kernel budget is changed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeNinePrimitive
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeThirdPrimitive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- A proved block iso equality gives the prescribed literal native nine factors. -/
theorem nativeNineFactor_of_blockIso
    {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (c₁₂ c₁₃ c₂₃ : Z ⟶ Y)
    (h₁ : c₁₂ ≫ f₁ = c₁₃ ≫ f₁) (h₂ : c₁₂ ≫ f₂ = c₂₃ ≫ f₁)
    (h₃ : c₁₃ ≫ f₂ = c₂₃ ≫ f₂)
    (hblocks : nativeDirectLineIso M f₁ f₂ ψ c₁₂ (c₁₃ ≫ f₁) (c₂₃ ≫ f₁) h₁ h₂ ≪≫
        nativeSecondLineIso M f₁ f₂ ψ c₂₃ (c₁₃ ≫ f₂) h₃ =
      nativeThirdLineIso M f₁ f₂ ψ c₁₃) :
    ((Scheme.Modules.pullbackCongr h₁).app M).symm ≪≫
      ((Scheme.Modules.pullbackComp c₁₂ f₁).app M).symm ≪≫
      (Scheme.Modules.pullback c₁₂).mapIso ψ ≪≫
      ((Scheme.Modules.pullbackComp c₁₂ f₂).app M) ≪≫
      ((Scheme.Modules.pullbackCongr h₂).app M) ≪≫
      ((Scheme.Modules.pullbackComp c₂₃ f₁).app M).symm ≪≫
      (Scheme.Modules.pullback c₂₃).mapIso ψ ≪≫
      ((Scheme.Modules.pullbackComp c₂₃ f₂).app M) ≪≫
      ((Scheme.Modules.pullbackCongr h₃).app M).symm =
    ((Scheme.Modules.pullbackComp c₁₃ f₁).app M).symm ≪≫
      (Scheme.Modules.pullback c₁₃).mapIso ψ ≪≫
      ((Scheme.Modules.pullbackComp c₁₃ f₂).app M) :=
  (nativeNineLineIso_blocks M f₁ f₂ ψ c₁₂ c₁₃ c₂₃ h₁ h₂ h₃).trans hblocks

#print axioms nativeNineFactor_of_blockIso

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
