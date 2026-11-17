/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Right translations and their action on field-valued points

The categorical precomposition identities are qualified as
CategoryTheory.MonObj.comp_one and CategoryTheory.MonObj.comp_mul.
Point identities use the underlying scheme compositions, the same group
inversion and the original field-valued points.

The group law, field, terminal-point carrier, public statements and
universe parameters are unchanged. These elementary morphism calculations
supply translation isomorphisms; they do not assert the theorem of the
square, ampleness, finiteness or the reduction criterion.
-/
import NativeDivisorKernel

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace H5OriginalDVR.Lane2.NativeTranslationAction

variable {K : Type u} [Field K]

/-- The literal K-point in the underlying scheme. -/
def point (A : Grp (Over (Spec (CommRingCat.of K))))
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) : A.X.left :=
  x.left (IsLocalRing.closedPoint K)

theorem rightTranslationOver_one (A : Grp (Over (Spec (CommRingCat.of K)))) :
    H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A
      (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) = 𝟙 A.X := by
  change (𝟙 A.X) * (toUnit A.X ≫ (1 : 𝟙_ _ ⟶ A.X)) = 𝟙 A.X
  rw [CategoryTheory.MonObj.comp_one, mul_one]

/-- Composition of the SAME right translations is the original point product. -/
theorem rightTranslationOver_comp (A : Grp (Over (Spec (CommRingCat.of K))))
    (x y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x ≫
      H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A y =
        H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A (x * y) := by
  have hc : H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x ≫ toUnit A.X =
      toUnit A.X := toUnit_unique _ _
  change H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x ≫
    ((𝟙 A.X) * (toUnit A.X ≫ y)) = _
  rw [CategoryTheory.MonObj.comp_mul, Category.comp_id, ← Category.assoc, hc]
  change ((𝟙 A.X) * (toUnit A.X ≫ x)) * (toUnit A.X ≫ y) =
    (𝟙 A.X) * (toUnit A.X ≫ (x * y))
  rw [mul_assoc, ← CategoryTheory.MonObj.comp_mul]

/-- The actual inverse is right translation by the original inverse point. -/
def rightTranslationOverIso (A : Grp (Over (Spec (CommRingCat.of K))))
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) : A.X ≅ A.X where
  hom := H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x
  inv := H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x⁻¹
  hom_inv_id := by rw [rightTranslationOver_comp, mul_inv_cancel, rightTranslationOver_one]
  inv_hom_id := by rw [rightTranslationOver_comp, inv_mul_cancel, rightTranslationOver_one]

def rightTranslationIso (A : Grp (Over (Spec (CommRingCat.of K))))
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) : A.X.left ≅ A.X.left :=
  (Over.forget (Spec (CommRingCat.of K))).mapIso (rightTranslationOverIso A x)

/-- The scalar scheme inversion is the SAME group object's inversion iso. -/
def inversionIso (A : Grp (Over (Spec (CommRingCat.of K)))) : A.X.left ≅ A.X.left :=
  (Over.forget (Spec (CommRingCat.of K))).mapIso (asIso ι[A.X])

/-- The original action on literal points, not a substitute point carrier. -/
theorem rightTranslation_apply_point (A : Grp (Over (Spec (CommRingCat.of K))))
    (x y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x (point A y) =
      point A (y * x) := by
  have hc : y ≫ toUnit A.X = 𝟙 (𝟙_ (Over (Spec (CommRingCat.of K)))) := toUnit_unique _ _
  have h : y ≫ H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x = y * x := by
    change y ≫ ((𝟙 A.X) * (toUnit A.X ≫ x)) = _
    rw [CategoryTheory.MonObj.comp_mul, Category.comp_id, ← Category.assoc, hc, Category.id_comp]
  have hleft : y.left ≫
      (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x).left = (y * x).left := by
    simpa only [Over.comp_left] using
      congrArg (fun f : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X => f.left) h
  change (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x).left
    (y.left (IsLocalRing.closedPoint K)) = (y * x).left (IsLocalRing.closedPoint K)
  calc
    (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x).left
        (y.left (IsLocalRing.closedPoint K)) =
      (y.left ≫ (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x).left)
        (IsLocalRing.closedPoint K) :=
      (_root_.AlgebraicGeometry.Scheme.Hom.comp_apply y.left
        (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A x).left
        (IsLocalRing.closedPoint K)).symm
    _ = (y * x).left (IsLocalRing.closedPoint K) :=
      congrArg (fun f : Spec (CommRingCat.of K) ⟶ A.X.left =>
        f (IsLocalRing.closedPoint K)) hleft

theorem inversion_apply_point (A : Grp (Over (Spec (CommRingCat.of K))))
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    ι[A.X].left (point A x) = point A x⁻¹ := by
  change ι[A.X].left (x.left (IsLocalRing.closedPoint K)) =
    (x⁻¹).left (IsLocalRing.closedPoint K)
  rw [CategoryTheory.Hom.inv_def, Over.comp_left]
  exact (_root_.AlgebraicGeometry.Scheme.Hom.comp_apply x.left ι[A.X].left
    (IsLocalRing.closedPoint K)).symm

end H5OriginalDVR.Lane2.NativeTranslationAction
