/-
NEW EDITION: p7o1 translation API repair, 2026-11-17.
Base SHA7fc6436943bed12ec75fc3b2135188fa44c6e91ea1738afeb7d339773af4a3d3.
The frozen base and Parent's failed full-closure log remain unchanged.
Pinned Mathlib Cartesian/Mon defines CategoryTheory.MonObj.comp_one and
CategoryTheory.MonObj.comp_mul; open scoped enables Hom operations, not
unqualified lemma resolution. Qualify those exact categorical lemmas.
The point equalities now use explicit underlying scheme compositions and
pinned Scheme.Hom.comp_apply / CategoryTheory.Hom.inv_def, including the
two point/coercion diagnostics in the same log. No public statement,
group law, field, point carrier, namespace, universe or option changes.
NEW Source only; Parent probes it. No lane compile, parser/AST/helper run.
-/
/-
H5 original-input Step2 / GM8: the actual right-translation isos and point actions.
Copyright (c) 2026 H5 lane2 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. Symbolic u, any field characteristic or dimension.

The group action is the SAME original Grp object, not an independent law.
These ordinary morphism calculations supply the actual invertible maps used
in the translated-divisor open-set argument. They do not prove the square,
basepoint freeness, finiteness, I0/I1/I2 or NOS. No Source/W07 alias or Fact.
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
