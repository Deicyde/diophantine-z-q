import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd.lean
Original Git blob: 7d62e1827c66fc88a63cef5879bcf5e720a32eb5
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd
h77_bridge_namespace
set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S S' Z X : Scheme.{u}} (z : Z ⟶ S) (f : X ⟶ S) (ι : S' ⟶ S) :
    IsIso
      (pullback.lift
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.fst z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.snd z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc, ← pullback.condition (f := z) (g := f)]; exact pullback.condition))
        (by rw [pullback.lift_snd, pullback.lift_snd]) :
        pullback (pullback.fst z f ≫ z) ι ⟶ pullback (pullback.snd z ι) (pullback.snd f ι)) := by

  have wA : (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst z ι) ≫ z =
      (pullback.snd (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.fst f ι) ≫ f := by
    have h1 : pullback.fst z ι ≫ z = pullback.snd z ι ≫ ι := pullback.condition
    have h2 : pullback.fst f ι ≫ f = pullback.snd f ι ≫ ι := pullback.condition
    have h3 : pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd z ι =
        pullback.snd (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd f ι := pullback.condition
    simp only [Category.assoc, h1, h2]
    rw [← Category.assoc, h3, Category.assoc]
  let A : pullback (pullback.snd z ι) (pullback.snd f ι) ⟶ pullback z f :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst z ι) (pullback.snd _ _ ≫ pullback.fst f ι) wA
  have hA1 : A ≫ pullback.fst z f = pullback.fst _ _ ≫ pullback.fst z ι := pullback.lift_fst _ _ _
  have hA2 : A ≫ pullback.snd z f = pullback.snd _ _ ≫ pullback.fst f ι := pullback.lift_snd _ _ _
  have wAB : A ≫ (pullback.fst z f ≫ z) = (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ pullback.snd z ι) ≫ ι := by
    rw [← Category.assoc, hA1, Category.assoc, Category.assoc]
    exact congrArg (pullback.fst (pullback.snd z ι) (pullback.snd f ι) ≫ ·) pullback.condition
  let inv : pullback (pullback.snd z ι) (pullback.snd f ι) ⟶ pullback (pullback.fst z f ≫ z) ι :=
    pullback.lift A (pullback.fst _ _ ≫ pullback.snd z ι) wAB
  have hI1 : inv ≫ pullback.fst (pullback.fst z f ≫ z) ι = A := pullback.lift_fst _ _ _
  have hI2 : inv ≫ pullback.snd (pullback.fst z f ≫ z) ι = pullback.fst _ _ ≫ pullback.snd z ι := pullback.lift_snd _ _ _
  refine ⟨⟨inv, ?_, ?_⟩⟩
  ·
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, reassoc_of% hI1, reassoc_of% hA1, hA1,
          pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [Category.assoc, Category.id_comp, reassoc_of% hI1, reassoc_of% hA2, hA2,
          pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_fst]
    · simp only [Category.assoc, Category.id_comp, reassoc_of% hI2, hI2,
        pullback.lift_fst_assoc, pullback.lift_snd]
  ·
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst_assoc, pullback.lift_fst,
          reassoc_of% hI1, hA1]
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst_assoc, pullback.lift_snd, hI2]
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_snd_assoc, pullback.lift_fst,
          reassoc_of% hI1, hA2]
      · simp only [Category.assoc, Category.id_comp, pullback.lift_snd_assoc, pullback.lift_snd, hI2]
        exact pullback.condition


end P2MW.S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
