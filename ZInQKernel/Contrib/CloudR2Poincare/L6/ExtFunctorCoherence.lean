import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Pointed exact-functor calculus for the EXISTING native cohomology map

H-72 L6. The W07 H-pullback is an Ext exact-functor map preceded by the
canonical constant-sheaf map. These elementary identities use the pinned
Mathlib Ext maps, with their original exactness hypotheses. They introduce
no cohomology model or geometric premise.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w₀ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ZInQ.Contrib.CloudR2Poincare.L6

section ThreeCategories

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasExt.{w₀} C] [HasExt.{w₁} D] [HasExt.{w₂} E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Composition of actual exact-functor Ext maps with actual source arrows. -/
theorem pointedExtMap_comp {K M : C} {K' : D} {K'' : E} (n : ℕ)
    (a : K' ⟶ F.obj K) (b : K'' ⟶ G.obj K') (z : Ext.{w₀} K M n) :
    (Ext.mk₀ b).comp
        (((Ext.mk₀ a).comp (z.mapExactFunctor F) (zero_add n)).mapExactFunctor G)
        (zero_add n) =
      (Ext.mk₀ (b ≫ G.map a)).comp (z.mapExactFunctor (F ⋙ G)) (zero_add n) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_mapExactFunctor]

end ThreeCategories

section TwoCategories

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w₀} C] [HasExt.{w₁} D]
  (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An actual natural transformation commutes with the pointed Ext map. -/
theorem pointedExtMap_natTrans {K M : C} {K' : D} (n : ℕ)
    (a : K' ⟶ F.obj K) (τ : F ⟶ G) (z : Ext.{w₀} K M n) :
    ((Ext.mk₀ a).comp (z.mapExactFunctor F) (zero_add n)).comp
        (Ext.mk₀ (τ.app M)) (add_zero n) =
      (Ext.mk₀ (a ≫ τ.app K)).comp (z.mapExactFunctor G) (zero_add n) := by
  rw [Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp, Ext.mk₀_comp_mk₀_assoc]

end TwoCategories

/-- The actual identity exact-functor map with the identity source arrow is identity. -/
theorem pointedExtMap_id {C : Type*} [Category* C] [Abelian C] [HasExt.{w₀} C]
    {K M : C} (n : ℕ) (z : Ext.{w₀} K M n) :
    (Ext.mk₀ (𝟙 K)).comp (z.mapExactFunctor (𝟭 C)) (zero_add n) = z := by
  rw [Ext.id_mapExactFunctor, Ext.mk₀_id_comp]

end ZInQ.Contrib.CloudR2Poincare.L6
