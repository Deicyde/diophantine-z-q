/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Translated sections of the native tensor square

For a line N and its given section theta, an actual square isomorphism
constructs the translated-pair section of the same native tensor power.
Translations use the original group law and terminal-point carrier.
The recursion tensorPow N 2 = N tensor (N tensor unit) is respected by
explicit unitors, not identified with a differently defined power.

The unit-translation calculation uses CategoryTheory.MonObj.comp_one.
The isomorphism argument is fixed-object data; this construction alone
does not assert the square theorem, nonvanishing, ampleness, finiteness
or the reduction criterion. All field characteristics and universes remain
as in the statements below.
-/
import NativeDivisorKernel
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeTranslatedPairSection

/-- The original right translation by its original unit point is identity.
No alternate identity point or group law is chosen. -/
theorem rightTranslation_one {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) :
    H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A
      (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) = 𝟙 A.X.left := by
  have h : H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslationOver A
      (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) = 𝟙 A.X := by
    change (𝟙 A.X) * (toUnit A.X ≫ (1 : 𝟙_ _ ⟶ A.X)) = 𝟙 A.X
    rw [CategoryTheory.MonObj.comp_one, mul_one]
  exact congrArg (fun f : A.X ⟶ A.X => f.left) h

/-- Convert the ACTUAL I5a iso at (x,x^-1) into the native pair-to-power2 iso,
using the actual identity-pullback map and the native recursion/unitor. -/
def pairIsoNativePowerTwo {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (N : A.X.left.Modules) [N.IsInvertible]
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)
    (eSquare :
      (Scheme.Modules.pullback
          (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A (x * x⁻¹))).obj N ⊗ N ≅
        (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).obj N ⊗
          (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹)).obj N) :
    (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).obj N ⊗
      (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹)).obj N ≅
        Scheme.Modules.tensorPow N 2 := by
  have ht : H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A (x * x⁻¹) =
      𝟙 A.X.left := by
    rw [mul_inv_cancel, rightTranslation_one]
  let et : (Scheme.Modules.pullback
      (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A (x * x⁻¹))).obj N ≅ N :=
    (Scheme.Modules.pullbackCongr ht).app N ≪≫ (Scheme.Modules.pullbackId A.X.left).app N
  exact eSquare.symm ≪≫ (et ⊗ᵢ Iso.refl N) ≪≫ whiskerLeftIso N (ρ_ N).symm

/-- The actual paired section theta_x tensor theta_-x of the SAME native
power2. Both theta_x are produced by actual pullback/unit maps from theta.
The supplied iso is earlier I5a output, not a chosen section/presentation.
No nonzero/basepoint-free claim is made by this construction alone. -/
def pairedSectionFromActualSquare {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N)
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)
    (eSquare :
      (Scheme.Modules.pullback
          (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A (x * x⁻¹))).obj N ⊗ N ≅
        (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).obj N ⊗
          (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹)).obj N) :
    Scheme.Modules.unit A.X.left ⟶ Scheme.Modules.tensorPow N 2 :=
  (λ_ (Scheme.Modules.unit A.X.left)).inv ≫
    (H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom
        (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x) N θ ⊗ₘ
      H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom
        (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹) N θ) ≫
    (pairIsoNativePowerTwo A N x eSquare).hom

end H5OriginalDVR.Lane2.NativeTranslatedPairSection
