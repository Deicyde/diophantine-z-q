/-
H5 lane3 Step 1: `GrpObjOfCompatibleMono` (ConstructorParts.lean) PROVED. This is pure category
theory in a cartesian monoidal category. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

Every group-object axiom for `(Z, e, m, i)` is checked after composing with the mono `j`
(`cancel_mono`), using the compatibilities `e ≫ j = η`, `m ≫ j = (j ⊗ j) ≫ μ`,
`i ≫ j = j ≫ ι` and the axioms of `G`:
* unit laws: `whisker…_comp_tensorHom`, `tensorHom_def(')`, the unitors' naturality;
* associativity: `tensorHom_comp_tensorHom`, `associator_naturality`;
* inverse laws: `lift_map` plus Mathlib `GrpObj.lift_comp_inv_left/right`.
`IsMonHom j` is exactly the two compatibilities.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.ConstructorAssembly

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem grpObjOfCompatibleMono : GrpObjOfCompatibleMono.{u} := by
  intro C _ _ G Z j _ e m i he hm hi
  -- interchange helpers
  have key₁ : ∀ {A B B' D E : C} (f : A ⟶ B) (g : B ⟶ B') (h : D ⟶ E),
      (f ≫ g) ⊗ₘ h = (f ⊗ₘ h) ≫ g ▷ E := by
    intro A B B' D E f g h
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have key₂ : ∀ {A B D E E' : C} (f : A ⟶ B) (g : D ⟶ E) (h : E ⟶ E'),
      f ⊗ₘ (g ≫ h) = (f ⊗ₘ g) ≫ B ◁ h := by
    intro A B D E E' f g h
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  -- the associativity computation, after composing with `j`
  have hassocL : (m ▷ Z ≫ m) ≫ j =
      ((j ⊗ₘ j) ⊗ₘ j) ≫ (α_ G.X G.X G.X).hom ≫ G.X ◁ μ[G.X] ≫ μ[G.X] := by
    rw [Category.assoc, hm, ← Category.assoc, whiskerRight_comp_tensorHom, hm, key₁,
      Category.assoc, MonObj.mul_assoc]
  have hassocR : ((α_ Z Z Z).hom ≫ Z ◁ m ≫ m) ≫ j =
      ((j ⊗ₘ j) ⊗ₘ j) ≫ (α_ G.X G.X G.X).hom ≫ G.X ◁ μ[G.X] ≫ μ[G.X] := by
    rw [Category.assoc, Category.assoc, hm, ← Category.assoc (Z ◁ m), whiskerLeft_comp_tensorHom,
      hm, key₂]
    simp only [Category.assoc]
    rw [← associator_naturality_assoc]
  let inst : GrpObj Z :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_mono j, Category.assoc, hm, ← Category.assoc, whiskerRight_comp_tensorHom, he,
          tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono j, Category.assoc, hm, ← Category.assoc, whiskerLeft_comp_tensorHom, he,
          MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono j, hassocL, hassocR]
      left_inv := by
        rw [← cancel_mono j, Category.assoc, hm, ← Category.assoc, lift_map, hi, Category.id_comp,
          GrpObj.lift_comp_inv_left, Category.assoc, he]
      right_inv := by
        rw [← cancel_mono j, Category.assoc, hm, ← Category.assoc, lift_map, hi, Category.id_comp,
          GrpObj.lift_comp_inv_right, Category.assoc, he] }
  exact ⟨inst, ⟨he, hm⟩⟩

/-- The constructor, with `GrpObjOfCompatibleMono` discharged. -/
theorem reducedSubgroupOfClosedSubset_of (hRed : IsReducedSubschemeVanishingIdeal.{u})
    (hGR : GeomReducedOverAlgClosed.{u}) : ReducedSubgroupOfClosedSubset.{u} :=
  reducedSubgroupOfClosedSubset hRed grpObjOfCompatibleMono hGR

end ZInQ.Contrib.CloudR2NOS.Step1
