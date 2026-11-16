/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Lean 4.35 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 compatibility layer for the
H5 lane4 port of anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
whose source was written against Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.

The declarations below restate, VERBATIM in statement and proof, API that Mathlib db584 had and
Mathlib 56a removed or moved, so that the vendored source keeps its original proof text.
They are isolated beneath the port prefix `ZInQ.Contrib.CloudW03NeronSurj.FLT` (nothing is added
to Mathlib's namespaces) and add no axiom.

Source of the restated material: Mathlib (https://github.com/leanprover-community/mathlib4)
at db584cd6d46c92f209a44c0f1c829460d327499d, file
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`,
Copyright (c) 2024 Joël Riou; Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou.
Released under the Apache License 2.0 (see Mathlib's LICENSE).

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), H5 lane4, 2026-11-14: extracted from the file above;
in Mathlib 56a the monoidal structure lives on `PresheafOfModulesOfCommRing R` (an abbreviation of
the same type `PresheafOfModules (R ⋙ forget₂ _ _)`) and its lemmas moved to namespace
`PresheafOfModulesOfCommRing`; the db584 `CommRing ((R ⋙ forget₂ _ RingCat).obj X)` instance was
deleted.  This file re-provides the db584 instance and lemma statements under the port prefix,
with `tensorObj` read as Mathlib 56a's `PresheafOfModulesOfCommRing.Monoidal.tensorObj`, and
without db584's `dsimp%` statement preprocessing (under Mathlib 56a's simp set `dsimp%` would
rewrite these left-hand sides into Mathlib 56a's new normal form; the plain statements are the
db584 lemmas' intended left-hand sides and are still proved by `rfl`).
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open CategoryTheory MonoidalCategory BraidedCategory Category Limits

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe v u v₁ u₁

section PresheafOfModulesMonoidal

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Mathlib db584 instance (deleted in 56a). -/
instance instCommRingObjCompForget₂RingCat (X : Cᵒᵖ) :
    CommRing ((R ⋙ forget₂ _ RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

namespace Monoidal

variable {M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X :))
      (β := fun _ ↦ (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X))
        ((PresheafOfModulesOfCommRing.Monoidal.tensorObj M₁ M₂).map f)) (m₁ ⊗ₜ[R.obj X] m₂) =
    M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

@[simp]
lemma tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom f g).app X = f.app X ⊗ₘ g.app X := rfl

end Monoidal

section

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

lemma tensorObj_obj (X : Cᵒᵖ) :
    (M₁ ⊗ M₂).obj X =
      MonoidalCategory.tensorObj (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

variable {M₂ M₃} in
@[simp]
lemma whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    (M₁ ◁ f).app X = whiskerLeft (C := ModuleCat (R.obj X)) (M₁.obj X) (f.app X) :=
  rfl

variable {M₁ M₂} in
@[simp]
lemma whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    (f ▷ M₃).app X = whiskerRight (C := ModuleCat (R.obj X)) (f.app X) (M₃.obj X) := rfl

variable {M₁ M₂ M₃ M₄} in
@[simp]
lemma tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    (f ⊗ₘ g).app X =
      MonoidalCategory.tensorHom (C := ModuleCat (R.obj X)) (f.app X) (g.app X) := rfl

@[simp]
lemma leftUnitor_hom_app (X : Cᵒᵖ) :
    (λ_ M₁).hom.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma leftUnitor_inv_app (X : Cᵒᵖ) :
    (λ_ M₁).inv.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv := by
  rfl

@[simp]
lemma rightUnitor_hom_app (X : Cᵒᵖ) :
    (ρ_ M₁).hom.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma rightUnitor_inv_app (X : Cᵒᵖ) :
    (ρ_ M₁).inv.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv :=
  rfl

@[simp]
lemma associator_hom_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).hom.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).hom :=
  rfl

@[simp]
lemma associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

@[simp]
lemma braiding_hom_app (X : Cᵒᵖ) :
    (braiding M₁ M₂).hom.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).hom := by
  rfl

@[simp]
lemma braiding_inv_app (X : Cᵒᵖ) :
    (braiding M₁ M₂).inv.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).inv := rfl

end

end PresheafOfModules

end PresheafOfModulesMonoidal

end ZInQ.Contrib.CloudW03NeronSurj.FLT
