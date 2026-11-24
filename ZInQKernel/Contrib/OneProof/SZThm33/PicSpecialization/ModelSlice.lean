import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RelativeDeltaIso
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.SliceTrivialization

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open Scheme.Modules
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

open PicDict.Transport

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

/-- The slice at a given section of the relative group. -/
def pointSlice (y : 𝟙_ (Over S) ⟶ G) : G ⟶ G ⊗ G := lift (𝟙 G) (toUnit G ≫ y)

/-- The slice at the identity in the second coordinate. -/
def firstAxis : G ⟶ G ⊗ G := lift (𝟙 G) (1 : G ⟶ G)

/-- The slice at the identity in the first coordinate. -/
def secondAxis : G ⟶ G ⊗ G := lift (1 : G ⟶ G) (𝟙 G)

/-- Multiplication by an integer in the model. -/
def multiplyBy (n : ℕ) : G ⟶ G := (𝟙 G) ^ n

/-- Right translation by a section. -/
def translateBy (x : 𝟙_ (Over S) ⟶ G) : G ⟶ G := 𝟙 G * (toUnit G ≫ x)

theorem pointSlice_comp_powerFirst (y : 𝟙_ (Over S) ⟶ G) (n : ℕ) :
    multiplyBy G n ≫ pointSlice G y = pointSlice G y ≫ powerFirst G n := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, pointSlice, powerFirst, lift_fst, Category.comp_id,
      MonObj.comp_pow, multiplyBy]
  · simp only [Category.assoc, pointSlice, powerFirst, lift_snd]
    rw [← Category.assoc, toUnit_unique (multiplyBy G n ≫ toUnit G) (toUnit G)]

theorem pointSlice_comp_powerSecond (y : 𝟙_ (Over S) ⟶ G) (n : ℕ) (hy : y ^ n = 1) :
    pointSlice G y ≫ powerSecond G n = firstAxis G := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [pointSlice, powerSecond, firstAxis, Category.assoc, lift_fst]
  · simp only [pointSlice, powerSecond, firstAxis, Category.assoc, lift_snd, MonObj.comp_pow]
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]

theorem translateBy_comp_multiplyBy [IsCommMonObj G]
    (x : 𝟙_ (Over S) ⟶ G) (n : ℕ) (hx : x ^ n = 1) :
    translateBy G x ≫ multiplyBy G n = multiplyBy G n := by
  simp only [translateBy, multiplyBy, MonObj.comp_pow, Category.comp_id]
  rw [mul_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, mul_one]

theorem map_productDeltaClass_firstAxis (L : G.left.Pic) :
    Scheme.Pic.map (firstAxis G).left (productDeltaClass G L) = 1 := by
  simp only [productDeltaClass, firstAxis, map_deltaClass, lift_fst, lift_snd, deltaClass_one_right]

theorem map_productDeltaClass_secondAxis (L : G.left.Pic) :
    Scheme.Pic.map (secondAxis G).left (productDeltaClass G L) = 1 := by
  simp only [productDeltaClass, secondAxis, map_deltaClass, lift_fst, lift_snd, deltaClass_one_left]

/-- An actual line in the normalized polarization class is trivial on both axes. -/
theorem nonempty_iso_axes (L : G.left.Pic) (M : (G ⊗ G).left.Modules) [M.IsInvertible]
    (hM : Scheme.Pic.mk M = productDeltaClass G L) :
    Nonempty (unit G.left ≅ (Scheme.Modules.pullback (firstAxis G).left).obj M) ∧
      Nonempty (unit G.left ≅ (Scheme.Modules.pullback (secondAxis G).left).obj M) := by
  constructor
  · apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
    rw [← Scheme.Pic.one_eq_mk_unit, ← Scheme.Pic.map_mk, hM, map_productDeltaClass_firstAxis]
  · apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
    rw [← Scheme.Pic.one_eq_mk_unit, ← Scheme.Pic.map_mk, hM, map_productDeltaClass_secondAxis]

/-- A multiplication comparison on the model gives an actual Mumford
trivialization on the slice at a torsion section of the model. -/
def pointSliceTriv (y : 𝟙_ (Over S) ⟶ G) (n : ℕ) (hy : y ^ n = 1)
    (M : (G ⊗ G).left.Modules)
    (J : (Scheme.Modules.pullback (powerFirst G n).left).obj M ≅
      (Scheme.Modules.pullback (powerSecond G n).left).obj M)
    (e : unit G.left ≅ (Scheme.Modules.pullback (firstAxis G).left).obj M) :
    unit G.left ≅ (Scheme.Modules.pullback (multiplyBy G n).left).obj
      ((Scheme.Modules.pullback (pointSlice G y).left).obj M) :=
  sliceComparisonTriv (multiplyBy G n).left (pointSlice G y).left (firstAxis G).left
    (powerFirst G n).left (powerSecond G n).left
    (congrArg Over.Hom.left (pointSlice_comp_powerFirst G y n))
    (congrArg Over.Hom.left (pointSlice_comp_powerSecond G y n hy)) M J e

/-- The slice is the actual polarization class when the base has trivial Picard group. -/
theorem map_productDeltaClass_pointSlice [Subsingleton S.Pic]
    (y : 𝟙_ (Over S) ⟶ G) (L : G.left.Pic) :
    Scheme.Pic.map (pointSlice G y).left (productDeltaClass G L) =
      Scheme.Pic.map (translateBy G y).left L * L⁻¹ := by
  have hs : Subsingleton (𝟙_ (Over S)).left.Pic := ‹Subsingleton S.Pic›
  have hOne : Scheme.Pic.map (1 : G ⟶ G).left L = 1 := by
    rw [CategoryTheory.Hom.one_def, Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one _ _ _
  have hPt : Scheme.Pic.map (toUnit G ≫ y).left L = 1 := by
    rw [Over.comp_left]
    exact ZInQ.Contrib.CloudR2Poincare.L6.pic_map_comp_eq_one _ _ _
  rw [productDeltaClass, map_deltaClass]
  simp only [pointSlice, lift_fst, lift_snd, deltaClass,
    hOne, hPt, mul_one, Over.id_left, Scheme.Pic.map_id, translateBy]

end ZInQ.ToricOrthogonality
