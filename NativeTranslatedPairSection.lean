/-
NEW EDITION: p7o1 paired-section composition API repair, 2026-11-17.
Base SHA68b32c9e2d1c4b69c273605c65343dc81f27c2d33bed9a4b924084bffdc0240c.
The frozen base and Parent's failed full-closure log remain unchanged.
Only qualify comp_one as the exact pinned CategoryTheory.MonObj.comp_one
from Cartesian/Mon436–437. No MonoidHom substitution, alternate identity,
new hypothesis, namespace, public statement, tensor recursion or option.
NEW Source only; Parent probes it. No lane compile/parser/AST/helper run.
-/
/-
H5 original-input Step2 / GM8: actual native translated-pair section data.
Copyright (c) 2026 H5 lane2 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. This constructs the literal section of the SAME
native N.tensorPow 2 from the SAME theta and an ACTUAL square-output iso.
It does not prove that square iso, basepoint freeness, finite presentation,
I1/I2, ampleness, or NOS. No square Fact or new section/model factory.

Named pending earlier supplier is I5a from the genuine H71 cube3b509d68 and
its real native context maps; the iso argument is fixed-object producer
DATA, never an extra hypothesis of NOS. All translations are the SAME
terminal-point right action, and all unit/pullback/tensor/power operations
are native W07. The actual recursion tensorPow 2 = N tensor (N tensor unit)
is respected by the explicit right unitor, not a Source/W07 power alias.

All symbolic u and any field characteristic/dimension. Source-write gate
c3e58087/d1346f11/86d27970 read; no Native/parser/helper/GET/root/budget action.
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
