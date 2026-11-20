import ZInQKernel.Contrib.CloudR2Poincare.L6.CubeGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual native cube faces are closed immersions

The original L6 base faces are sections of the actual product projections.
Separatedness makes these sections closed immersions; a genuine pullback square
then proves the literal nativeCubeFaceXR/YR maps are closed, hence affine.
No supplied affine-face, model, or replacement face arrow is used.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L4.CubeFaces

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}

/-- The literal X-base face is a section of the actual first projection. -/
theorem nativeCubeFaceXBase_fst
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceXBase f g y hy ≫ pullback.fst f g = 𝟙 X := by
  simp [L6.nativeCubeFaceXBase]

/-- The literal Y-base face is a section of the actual second projection. -/
theorem nativeCubeFaceYBase_snd
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    L6.nativeCubeFaceYBase f g x hx ≫ pullback.snd f g = 𝟙 Y := by
  simp [L6.nativeCubeFaceYBase]

/-- Separatedness alone makes the actual native X-base face closed. -/
theorem isClosedImmersion_nativeCubeFaceXBase
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated g]
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    IsClosedImmersion (L6.nativeCubeFaceXBase f g y hy) := by
  haveI : IsClosedImmersion
      (L6.nativeCubeFaceXBase f g y hy ≫ pullback.fst f g) := by
    rw [nativeCubeFaceXBase_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst f g)

/-- Separatedness alone makes the actual native Y-base face closed. -/
theorem isClosedImmersion_nativeCubeFaceYBase
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated f]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    IsClosedImmersion (L6.nativeCubeFaceYBase f g x hx) := by
  haveI : IsClosedImmersion
      (L6.nativeCubeFaceYBase f g x hx ≫ pullback.snd f g) := by
    rw [nativeCubeFaceYBase_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd f g)

/-- The actual X-family face square is Cartesian, by genuine pullback pasting. -/
theorem nativeCubeFaceXR_isPullback
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    IsPullback (pullback.fst f a) (L6.nativeCubeFaceXR f g a y hy)
      (L6.nativeCubeFaceXBase f g y hy)
      (pullback.fst (pullback.fst f g ≫ f) a) := by
  have hs : IsPullback (pullback.fst f a)
      (L6.nativeCubeFaceXR f g a y hy ≫ pullback.snd (pullback.fst f g ≫ f) a)
      (L6.nativeCubeFaceXBase f g y hy ≫ (pullback.fst f g ≫ f)) a := by
    rw [L6.nativeCubeFaceXR_struct, L6.nativeCubeFaceXBase_struct]
    exact IsPullback.of_hasPullback f a
  exact hs.of_bot (by simp [L6.nativeCubeFaceXR])
    (IsPullback.of_hasPullback (pullback.fst f g ≫ f) a)

/-- The actual Y-family face square is Cartesian, by genuine pullback pasting. -/
theorem nativeCubeFaceYR_isPullback
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    IsPullback (pullback.fst g a) (L6.nativeCubeFaceYR f g a x hx)
      (L6.nativeCubeFaceYBase f g x hx)
      (pullback.fst (pullback.fst f g ≫ f) a) := by
  have hs : IsPullback (pullback.fst g a)
      (L6.nativeCubeFaceYR f g a x hx ≫ pullback.snd (pullback.fst f g ≫ f) a)
      (L6.nativeCubeFaceYBase f g x hx ≫ (pullback.fst f g ≫ f)) a := by
    rw [L6.nativeCubeFaceYR_struct, L6.nativeCubeFaceYBase_struct]
    exact IsPullback.of_hasPullback g a
  exact hs.of_bot (by simp [L6.nativeCubeFaceYR])
    (IsPullback.of_hasPullback (pullback.fst f g ≫ f) a)

/-- The literal pullback.map X-face is closed; no affine-face premise is supplied. -/
theorem nativeCubeFaceXR_isClosedImmersion
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated g]
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    IsClosedImmersion (L6.nativeCubeFaceXR f g a y hy) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (nativeCubeFaceXR_isPullback f g a y hy)
    (isClosedImmersion_nativeCubeFaceXBase f g y hy)

/-- The literal pullback.map Y-face is closed; no affine-face premise is supplied. -/
theorem nativeCubeFaceYR_isClosedImmersion
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated f]
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    IsClosedImmersion (L6.nativeCubeFaceYR f g a x hx) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (nativeCubeFaceYR_isPullback f g a x hx)
    (isClosedImmersion_nativeCubeFaceYBase f g x hx)

/-- The actual X-family face is affine, as a closed immersion. -/
theorem nativeCubeFaceXR_isAffineHom
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated g]
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    IsAffineHom (L6.nativeCubeFaceXR f g a y hy) := by
  haveI := nativeCubeFaceXR_isClosedImmersion f g a y hy
  infer_instance

/-- The actual Y-family face is affine, as a closed immersion. -/
theorem nativeCubeFaceYR_isAffineHom
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [IsSeparated f]
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    IsAffineHom (L6.nativeCubeFaceYR f g a x hx) := by
  haveI := nativeCubeFaceYR_isClosedImmersion f g a x hx
  infer_instance

end ZInQ.Contrib.CloudR2Poincare.L4.CubeFaces
