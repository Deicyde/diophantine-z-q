/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Reflect actual group compatibility through a faithful monoidal functor.
Only injectivity on morphisms is needed: no fully faithful scheme pullback
or hdesc/group-law premise is introduced. The lemma applies to the real
fpqc base-change functor when upgrading the original generic comparison.
-/
import Mathlib.CategoryTheory.Monoidal.Mon

set_option autoImplicit false
noncomputable section
universe v₁ u₁ v₂ u₂
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- A faithful monoidal functor reflects the ACTUAL unit/multiplication
    diagrams on the given objects, with their given monoid structures. -/
theorem isMonHom_of_faithful_map
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Faithful] [F.Monoidal]
    {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (hf : IsMonHom (F.map f)) : IsMonHom f := by
  constructor
  · apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    simpa only [Functor.map_comp, Category.assoc, Functor.obj.η_def] using hf.one_hom
  · apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ F X X)).mp
    simpa only [Functor.map_comp, Category.assoc, Functor.obj.μ_def,
      Functor.LaxMonoidal.μ_natural_assoc] using hf.mul_hom

#print axioms isMonHom_of_faithful_map

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
