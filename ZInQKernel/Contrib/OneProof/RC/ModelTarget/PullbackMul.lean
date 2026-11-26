import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! Points of a base-changed group object multiply as their images in the original
group object. For `F = Over.pullback f` and `a b : P ⟶ F.obj E`, the product taken with
the group law induced by `F` maps to the product of the two composites with the first
projection. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {X Y : Scheme.{0}} (f : Y ⟶ X) (E : Over X) {P : Over Y}

/-- A point of the base change, read as a point of `E` over the composite. -/
def upHom (a : P ⟶ (Over.pullback f).obj E) : Over.mk (P.hom ≫ f) ⟶ E :=
  Over.homMk (a.left ≫ pullback.fst E.hom f) (by
    change (a.left ≫ pullback.fst E.hom f) ≫ E.hom = P.hom ≫ f
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w a)

@[simp] theorem upHom_left (a : P ⟶ (Over.pullback f).obj E) :
    (upHom f E a).left = a.left ≫ pullback.fst E.hom f := rfl

theorem pullback_map_left_fst {E E' : Over X} (k : E ⟶ E') :
    ((Over.pullback f).map k).left ≫ pullback.fst E'.hom f = pullback.fst E.hom f ≫ k.left := by
  simp

variable [MonObj E]

theorem mul_left_fst (a b : P ⟶ (Over.pullback f).obj E) :
    (a * b).left ≫ pullback.fst E.hom f = (lift (upHom f E a) (upHom f E b) ≫ μ[E]).left := by
  rw [Hom.mul_def, Functor.obj.μ_def]
  simp only [Over.comp_left, Category.assoc]
  rw [pullback_map_left_fst]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · have h1 := pullback_map_left_fst f (fst E E)
    rw [Category.assoc, ← Over.fst_left, ← h1, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, Category.assoc, Functor.Monoidal.μ_fst, lift_fst,
      ← Over.comp_left, lift_fst, upHom_left]
  · have h1 := pullback_map_left_fst f (snd E E)
    rw [Category.assoc, ← Over.snd_left, ← h1, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, Category.assoc, Functor.Monoidal.μ_snd, lift_snd,
      ← Over.comp_left, lift_snd, upHom_left]

#print axioms mul_left_fst

end ZInQ.Manuscript.RC.ModelTarget
