import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelSlice

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

variable {S W : Scheme.{0}} (G : Over S) [GrpObj G] (j : W ⟶ S)

local instance : GrpObj (Functor.obj (Over.pullback j) G) := Functor.grpObjObj

/-- Multiplication commutes with the projection from the base-changed group. -/
theorem testModel_projection_multiply (n : ℕ) :
    (multiplyBy (Functor.obj (Over.pullback j) G) n).left ≫ (pullback.fst G.hom j) = (pullback.fst G.hom j) ≫ (multiplyBy G n).left := by
  have hmap : (Over.pullback j).map (multiplyBy G n) = multiplyBy (Functor.obj (Over.pullback j) G) n := by
    unfold multiplyBy
    change (Over.pullback j).homMonoidHom ((𝟙 G) ^ n) = (𝟙 (Functor.obj (Over.pullback j) G)) ^ n
    rw [map_pow]
    change ((Over.pullback j).map (𝟙 G)) ^ n = (𝟙 (Functor.obj (Over.pullback j) G)) ^ n
    rw [CategoryTheory.Functor.map_id (Over.pullback j)]
  rw [← hmap]
  exact pullback.lift_fst _ _ _

private theorem multiplyBy_zero_left {B : Scheme.{0}} (V : Over B) [GrpObj V] :
    (multiplyBy V 0).left = V.hom ≫ η[V].left := by
  simp only [multiplyBy, pow_zero, CategoryTheory.Hom.one_def, Over.comp_left]
  rfl

/-- The zero section of a base change maps to the original zero section. -/
theorem testModel_projection_origin :
    η[(Functor.obj (Over.pullback j) G)].left ≫ (pullback.fst G.hom j) = j ≫ η[G].left := by
  have z := testModel_projection_multiply G j 0
  rw [multiplyBy_zero_left, multiplyBy_zero_left, Category.assoc] at z
  have hz : (Functor.obj (Over.pullback j) G).hom ≫ (η[(Functor.obj (Over.pullback j) G)].left ≫ (pullback.fst G.hom j)) =
      (Functor.obj (Over.pullback j) G).hom ≫ (j ≫ η[G].left) := z.trans
    ((congrArg (· ≫ η[G].left) (pullback.condition (f := G.hom) (g := j))).trans
      (Category.assoc _ _ _))
  have hη : η[(Functor.obj (Over.pullback j) G)].left ≫ (Functor.obj (Over.pullback j) G).hom = 𝟙 W := Over.w η[(Functor.obj (Over.pullback j) G)]
  have h := congrArg (η[(Functor.obj (Over.pullback j) G)].left ≫ ·) hz
  rw [← Category.assoc η[(Functor.obj (Over.pullback j) G)].left (Functor.obj (Over.pullback j) G).hom _,
    ← Category.assoc η[(Functor.obj (Over.pullback j) G)].left (Functor.obj (Over.pullback j) G).hom _,
    hη] at h
  exact (Category.id_comp (η[(Functor.obj (Over.pullback j) G)].left ≫ (pullback.fst G.hom j))).symm.trans
    (h.trans (Category.id_comp (j ≫ η[G].left)))

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.testModel_projection_multiply
#print axioms ZInQ.ToricOrthogonality.testModel_projection_origin
