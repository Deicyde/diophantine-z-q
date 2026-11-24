import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelSlice
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.AxisFrameRestriction

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

open PicDict.Transport

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem axisFirst_comp_powerFirst (n : ℕ) :
    firstAxis G ≫ powerFirst G n = multiplyBy G n ≫ firstAxis G := by
  have h : firstAxis G = pointSlice G η[G] := rfl
  rw [h, pointSlice_comp_powerFirst]

theorem axisFirst_comp_powerSecond (n : ℕ) :
    firstAxis G ≫ powerSecond G n = 𝟙 G ≫ firstAxis G := by
  have h : firstAxis G = pointSlice G η[G] := rfl
  have hη : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by simp [CategoryTheory.Hom.one_def]
  rw [Category.id_comp, h]
  exact pointSlice_comp_powerSecond G η[G] n (by rw [hη, one_pow])

theorem axisSecond_comp_powerFirst (n : ℕ) :
    secondAxis G ≫ powerFirst G n = 𝟙 G ≫ secondAxis G := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [secondAxis, powerFirst, Category.assoc, lift_fst, MonObj.comp_pow, one_pow,
      Category.id_comp]
  · simp only [secondAxis, powerFirst, Category.assoc, lift_snd, Category.id_comp]

theorem axisSecond_comp_powerSecond (n : ℕ) :
    secondAxis G ≫ powerSecond G n = multiplyBy G n ≫ secondAxis G := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [secondAxis, powerSecond, Category.assoc, lift_fst, MonObj.comp_one]
  · simp only [secondAxis, powerSecond, Category.assoc, lift_snd, MonObj.comp_pow,
      Category.comp_id, multiplyBy]

theorem axisOrigin_eq : (η[G] : 𝟙_ (Over S) ⟶ G) ≫ firstAxis G = η[G] ≫ secondAxis G := by
  have hη : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by simp [CategoryTheory.Hom.one_def]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [firstAxis, secondAxis, Category.assoc, lift_fst, MonObj.comp_one,
      Category.comp_id, hη]
  · simp only [firstAxis, secondAxis, Category.assoc, lift_snd, MonObj.comp_one,
      Category.comp_id, hη]

theorem origin_comp_multiply (n : ℕ) : η[G] ≫ multiplyBy G n = η[G] := by
  have hη : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by simp [CategoryTheory.Hom.one_def]
  simp only [multiplyBy, MonObj.comp_pow, Category.comp_id, hη, one_pow]

/-- The multiplication comparison in the chosen frame of the first axis. -/
def firstAxisDefect (n : ℕ) (M : (G ⊗ G).left.Modules)
    (J : (pullback (powerFirst G n).left).obj M ≅ (pullback (powerSecond G n).left).obj M)
    (e : unit G.left ≅ (pullback (firstAxis G).left).obj M) :=
  comparisonDefect (firstAxis G).left (multiplyBy G n).left (𝟙 G.left)
    (powerFirst G n).left (powerSecond G n).left
    (congrArg Over.Hom.left (axisFirst_comp_powerFirst G n))
    (congrArg Over.Hom.left (axisFirst_comp_powerSecond G n)) M J e

/-- The multiplication comparison in the chosen frame of the second axis. -/
def secondAxisDefect (n : ℕ) (M : (G ⊗ G).left.Modules)
    (J : (pullback (powerFirst G n).left).obj M ≅ (pullback (powerSecond G n).left).obj M)
    (e : unit G.left ≅ (pullback (secondAxis G).left).obj M) :=
  comparisonDefect (secondAxis G).left (𝟙 G.left) (multiplyBy G n).left
    (powerFirst G n).left (powerSecond G n).left
    (congrArg Over.Hom.left (axisSecond_comp_powerFirst G n))
    (congrArg Over.Hom.left (axisSecond_comp_powerSecond G n)) M J e

/-- Axis defects agree at the origin for compatible line frames. -/
theorem axisDefect_origin_eq (n : ℕ) (M : (G ⊗ G).left.Modules)
    (J : (pullback (powerFirst G n).left).obj M ≅ (pullback (powerSecond G n).left).obj M)
    (e₁ : unit G.left ≅ (pullback (firstAxis G).left).obj M)
    (e₂ : unit G.left ≅ (pullback (secondAxis G).left).obj M)
    (he : pullFramedAlong η[G].left (firstAxis G).left e₁ ≪≫
      (pullbackCongr (congrArg Over.Hom.left (axisOrigin_eq G))).app M =
        pullFramedAlong η[G].left (secondAxis G).left e₂) :
    pullUnitIso η[G].left (firstAxisDefect G n M J e₁) =
      pullUnitIso η[G].left (secondAxisDefect G n M J e₂) := by
  have hu : η[G].left ≫ (multiplyBy G n).left = η[G].left :=
    congrArg Over.Hom.left (origin_comp_multiply G n)
  apply pullUnitIso_comparisonDefect_of_common_restriction _ _ _ _
    (congrArg Over.Hom.left (axisOrigin_eq G)) _ _ _ _ (𝟙 S) (𝟙 S)
  · exact hu.trans (Category.id_comp _).symm
  · simp
  · simp
  · exact hu.trans (Category.id_comp _).symm
  · exact he

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.axisDefect_origin_eq
