/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Exact native pullbackComp/pullbackCongr normalization for the canonical line
cocycle. This file does not supply the global triple equation or M extension.
It retains the literal native functor and all actual composite maps, so the
remaining triple equation must be proved rather than renamed as a Fact.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

@[simp]
theorem native_pullbackCongr_self_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    ((Scheme.Modules.pullbackCongr (rfl : f = f)).app M).hom = 𝟙 _ := rfl

@[simp]
theorem native_pullbackCongr_self_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    ((Scheme.Modules.pullbackCongr (rfl : f = f)).app M).inv = 𝟙 _ := rfl

@[simp]
theorem native_pullbackCongr_symm_hom {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) :
    ((Scheme.Modules.pullbackCongr h.symm).app M).hom =
      ((Scheme.Modules.pullbackCongr h).app M).inv := by
  cases h
  rfl

@[simp]
theorem native_pullbackCongr_symm_hom_nat {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h.symm).hom.app M =
      (Scheme.Modules.pullbackCongr h).inv.app M := by
  cases h
  rfl

@[simp]
theorem native_pullbackCongr_self_hom_nat {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ := rfl

@[simp]
theorem native_pullbackCongr_self_inv_nat {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).inv.app M = 𝟙 _ := rfl

/-- Actual pseudofunctor pullback, including BOTH specified composite-map equalities. -/
theorem native_pullHom_explicit
    {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := modulesPseudofunctor) φ g gf₁ gf₂ h₁ h₂ =
      ((Scheme.Modules.pullbackCongr h₁).app M₁).inv ≫
      ((Scheme.Modules.pullbackComp g f₁).app M₁).inv ≫
      (Scheme.Modules.pullback g).map φ ≫
      ((Scheme.Modules.pullbackComp g f₂).app M₂).hom ≫
      ((Scheme.Modules.pullbackCongr h₂).app M₂).hom := by
  subst gf₁ gf₂
  simpa only [native_pullbackCongr_self_hom_nat, native_pullbackCongr_self_inv_nat,
    Iso.app_hom, Iso.app_inv, Category.id_comp, Category.comp_id] using modulesPseudofunctor_pullHom_eq φ g

/-- The LITERAL nine-factor native hom expression is the coherent pullHom
12/23 composition, with the exact nerve equations and coefficient maps. -/
theorem native_nineFactor_hom
    {X Y Z : Scheme.{u}} (M : X.Modules) (f₁ f₂ : Y ⟶ X)
    (ψ : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (c₁₂ c₁₃ c₂₃ : Z ⟶ Y)
    (h₁ : c₁₂ ≫ f₁ = c₁₃ ≫ f₁)
    (h₂ : c₁₂ ≫ f₂ = c₂₃ ≫ f₁)
    (h₃ : c₁₃ ≫ f₂ = c₂₃ ≫ f₂) :
    (((Scheme.Modules.pullbackCongr h₁).app M).symm ≪≫
      ((Scheme.Modules.pullbackComp c₁₂ f₁).app M).symm ≪≫
      (Scheme.Modules.pullback c₁₂).mapIso ψ ≪≫
      ((Scheme.Modules.pullbackComp c₁₂ f₂).app M) ≪≫
      ((Scheme.Modules.pullbackCongr h₂).app M) ≪≫
      ((Scheme.Modules.pullbackComp c₂₃ f₁).app M).symm ≪≫
      (Scheme.Modules.pullback c₂₃).mapIso ψ ≪≫
      ((Scheme.Modules.pullbackComp c₂₃ f₂).app M) ≪≫
      ((Scheme.Modules.pullbackCongr h₃).app M).symm).hom =
    pullHom (F := modulesPseudofunctor) ψ.hom c₁₂
        (c₁₃ ≫ f₁) (c₂₃ ≫ f₁) h₁ h₂ ≫
      pullHom (F := modulesPseudofunctor) ψ.hom c₂₃
        (c₂₃ ≫ f₁) (c₁₃ ≫ f₂) rfl h₃.symm := by
  rw [native_pullHom_explicit, native_pullHom_explicit]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    native_pullbackCongr_self_inv_nat, native_pullbackCongr_symm_hom,
    Iso.app_hom, Iso.app_inv, native_pullbackCongr_symm_hom_nat,
    Category.id_comp, Category.comp_id, Category.assoc]
  all_goals rfl

#print axioms native_pullHom_explicit
#print axioms native_nineFactor_hom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
