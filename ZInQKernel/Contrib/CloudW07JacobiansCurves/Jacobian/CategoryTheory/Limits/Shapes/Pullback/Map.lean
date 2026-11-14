-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.CategoryTheory.Limits.Shapes.Pullback.Map), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cartesian maps between pullbacks

Changing one leg of a cospan induces a Cartesian map between its pullbacks.
-/

namespace CategoryTheory.Limits

variable {categoryType : Type*} [Category* categoryType] [HasPullbacks categoryType]

/-- Changing the second leg of a cospan gives a base change of that morphism. -/
lemma isPullback_pullback_map {firstObject baseObject sourceObject targetObject : categoryType}
    (firstMap : firstObject ⟶ baseObject) (sourceMap : sourceObject ⟶ baseObject)
    (targetMap : targetObject ⟶ baseObject) (transition : sourceObject ⟶ targetObject)
    (compatible : transition ≫ targetMap = sourceMap) :
    IsPullback (pullback.map firstMap sourceMap firstMap targetMap
      (𝟙 firstObject) transition (𝟙 baseObject) (by simp) (by simp [compatible]))
      (pullback.snd firstMap sourceMap) (pullback.snd firstMap targetMap) transition := by
  refine IsPullback.of_right ?_ (by simp only [pullback.map, pullback.lift_snd])
    (IsPullback.of_hasPullback firstMap targetMap)
  have projection_eq : pullback.map firstMap sourceMap firstMap targetMap
      (𝟙 firstObject) transition (𝟙 baseObject) (by simp) (by simp [compatible]) ≫
        pullback.fst firstMap targetMap = pullback.fst firstMap sourceMap := by
    simp only [pullback.map, pullback.lift_fst, Category.comp_id]
  rw [projection_eq]
  simpa [compatible] using IsPullback.of_hasPullback firstMap sourceMap

/-- Changing the first leg of a cospan gives a base change of that morphism. -/
lemma isPullback_pullback_map_left
    {sourceObject targetObject baseObject extensionObject : categoryType}
    (transition : sourceObject ⟶ targetObject) (targetMap : targetObject ⟶ baseObject)
    (extensionMap : extensionObject ⟶ baseObject) :
    IsPullback (pullback.fst (transition ≫ targetMap) extensionMap)
      (pullback.map (transition ≫ targetMap) extensionMap targetMap extensionMap
        transition (𝟙 extensionObject) (𝟙 baseObject) (by simp) (by simp))
      transition (pullback.fst targetMap extensionMap) := by
  refine IsPullback.of_bot ?_ (by simp only [pullback.map, pullback.lift_fst])
    (IsPullback.of_hasPullback targetMap extensionMap)
  have projection_eq :
      pullback.map (transition ≫ targetMap) extensionMap targetMap extensionMap
          transition (𝟙 extensionObject) (𝟙 baseObject) (by simp) (by simp) ≫
        pullback.snd targetMap extensionMap = pullback.snd (transition ≫ targetMap) extensionMap := by
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  rw [projection_eq]
  exact IsPullback.of_hasPullback (transition ≫ targetMap) extensionMap

end CategoryTheory.Limits
