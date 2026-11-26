import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.RingTheory.TensorProduct.Basic

/-! Bundled finite tensor prefixes and their direct limit. -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace CountableTensorRefinement

universe u

variable {A : Type u} [CommRing A] (C : ℕ → CommAlgCat.{u} A)

/-- The prefix at `n` contains the factors with indices strictly below `n`. -/
def stage : ℕ → CommAlgCat.{u} A :=
  Nat.rec (motive := fun _ ↦ CommAlgCat.{u} A) (CommAlgCat.of A A)
    (fun n prev ↦ CommAlgCat.of A (prev ⊗[A] C n))

@[simp] theorem stage_zero : stage C 0 = CommAlgCat.of A A := rfl

theorem stage_succ (n : ℕ) :
    stage C (n + 1) = CommAlgCat.of A (stage C n ⊗[A] C n) := rfl

/-- The transition `b ↦ b ⊗ₜ 1`. -/
def leftInclusion (n : ℕ) : stage C n ⟶ stage C (n + 1) :=
  CommAlgCat.ofHom
    (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := stage C n) (B := C n))

/-- The new factor enters the next stage by `c ↦ 1 ⊗ₜ c`. -/
def rightInclusion (n : ℕ) : C n ⟶ stage C (n + 1) :=
  CommAlgCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := stage C n) (B := C n))

/-- The left inclusions determine the whole diagram indexed by `ℕ`. -/
def diagram : ℕ ⥤ CommAlgCat.{u} A :=
  Functor.ofSequence (X := stage C) (leftInclusion C)

@[simp] theorem diagram_map_succ (n : ℕ) :
    (diagram C).map (homOfLE (Nat.le_add_right n 1)) = leftInclusion C n :=
  Functor.ofSequence_map_homOfLE_succ (leftInclusion C) n

abbrev StageType (n : ℕ) : Type u := stage C n

abbrev TransitionHom (i j : ℕ) : Type u := StageType C i →ₐ[A] StageType C j

/-- Keep the transition algebra-hom-valued for Mathlib's hom-polymorphic `DirectLimit`. -/
def transition (i j : ℕ) (h : i ≤ j) : TransitionHom C i j :=
  ((diagram C).map (homOfLE h)).hom

instance instStageDirectedSystem : DirectedSystem (StageType C) (transition C · · ·) where
  map_self := by
    intro i x
    let F := diagram C
    have h : homOfLE (le_rfl : i ≤ i) = 𝟙 i := Subsingleton.elim _ _
    have hmap : F.map (homOfLE (le_rfl : i ≤ i)) = 𝟙 (F.obj i) :=
      (congrArg (fun a : i ⟶ i => F.map a) h).trans (F.map_id i)
    exact congrArg (fun a : F.obj i ⟶ F.obj i => a.hom (show F.obj i from x)) hmap
  map_map := by
    intro k j i hij hjk x
    change ((diagram C).map (homOfLE hjk)).hom
        (((diagram C).map (homOfLE hij)).hom x) =
      ((diagram C).map (homOfLE (hij.trans hjk))).hom x
    rw [← homOfLE_comp hij hjk, Functor.map_comp, CommAlgCat.hom_comp]
    rfl

/-- The actual quotient direct limit of the tensor prefixes. -/
abbrev LimitType : Type u :=
  DirectLimit (T := fun {i j} _ ↦ TransitionHom C i j) (StageType C) (transition C)

/-- The quotient direct limit, bundled as a commutative `A`-algebra. -/
def limit : CommAlgCat.{u} A := CommAlgCat.of A (LimitType C)

/-- The canonical map of the `n`-th prefix into the direct limit. -/
def toLimit (n : ℕ) : stage C n ⟶ limit C :=
  CommAlgCat.ofHom
    (DirectLimit.Algebra.of (R := A) (T := fun {i j} _ ↦ TransitionHom C i j)
      (StageType C) (transition C) n)

@[reassoc] theorem map_toLimit {i j : ℕ} (h : i ≤ j) :
    (diagram C).map (homOfLE h) ≫ toLimit C j = toLimit C i := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact DirectLimit.Algebra.of_f (R := A) (G := StageType C)
    (T := fun {i j} _ ↦ TransitionHom C i j) (f := transition C) h x

/-- The map from the base, given by the canonical leg at stage zero. -/
def baseToLimit : CommAlgCat.of A A ⟶ limit C := toLimit C 0

/-- The map from `C n` factors through the prefix at `n + 1`. -/
def factorToLimit (n : ℕ) : C n ⟶ limit C :=
  rightInclusion C n ≫ toLimit C (n + 1)

@[simp] theorem baseToLimit_toRingHom :
    (baseToLimit C).hom.toRingHom = algebraMap A (limit C) := by
  have h : (baseToLimit C).hom = Algebra.ofId A (limit C) :=
    Algebra.ext_id _ _ _
  exact congrArg AlgHom.toRingHom h

/-- The ring-map triangle from `A` through `C n` to the direct limit. -/
theorem factorToLimit_triangle (n : ℕ) :
    (factorToLimit C n).hom.toRingHom.comp (algebraMap A (C n)) =
      (baseToLimit C).hom.toRingHom :=
  ((factorToLimit C n).hom.comp_algebraMap).trans (baseToLimit_toRingHom C).symm

end CountableTensorRefinement
