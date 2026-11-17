import ZInQKernel.Contrib.CloudR2Poincare.L6.FaceInitialFacts
import ZInQKernel.Contrib.CloudR2Poincare.L6.ReducedCubeGluing
/-!
# Actual native opening faces and normalization

All face maps are literal pullback.map of the pointed product faces.
Normalization along the actual zero section is DERIVED from an entire face,
not supplied as an extra premise in the reduced opening telescope.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace ZInQ.Contrib.CloudR2Poincare.L6

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}

def nativeCubeFaceXBase (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) : X ⟶ pullback f g :=
  pullback.lift (𝟙 X) (f ≫ y) (by simp [Category.assoc, hy])
def nativeCubeFaceYBase (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) : Y ⟶ pullback f g :=
  pullback.lift (g ≫ x) (𝟙 Y) (by simp [Category.assoc, hx])

@[reassoc] theorem nativeCubeFaceXBase_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    nativeCubeFaceXBase f g y hy ≫ (pullback.fst f g ≫ f) = f := by
  simp [nativeCubeFaceXBase]
@[reassoc] theorem nativeCubeFaceYBase_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    nativeCubeFaceYBase f g x hx ≫ (pullback.fst f g ≫ f) = g := by
  simp [nativeCubeFaceYBase, Category.assoc, hx]

/-- Literal base change of the X-face; exact §6 map type. -/
def nativeCubeFaceXR (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    pullback f a ⟶ pullback (pullback.fst f g ≫ f) a :=
  pullback.map f a (pullback.fst f g ≫ f) a (nativeCubeFaceXBase f g y hy) (𝟙 Z) (𝟙 _)
    (by simp [nativeCubeFaceXBase_struct]) (by simp)
/-- Literal base change of the Y-face; exact §6 map type. -/
def nativeCubeFaceYR (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    pullback g a ⟶ pullback (pullback.fst f g ≫ f) a :=
  pullback.map g a (pullback.fst f g ≫ f) a (nativeCubeFaceYBase f g x hx) (𝟙 Z) (𝟙 _)
    (by simp [nativeCubeFaceYBase_struct]) (by simp)

@[reassoc] theorem nativeCubeFaceXR_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    nativeCubeFaceXR f g a y hy ≫ pullback.snd (pullback.fst f g ≫ f) a = pullback.snd f a := by
  simp [nativeCubeFaceXR]
@[reassoc] theorem nativeCubeFaceYR_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    nativeCubeFaceYR f g a x hx ≫ pullback.snd (pullback.fst f g ≫ f) a = pullback.snd g a := by
  simp [nativeCubeFaceYR]

def nativeCubePoint (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) : Spec (.of k) ⟶ pullback f g :=
  pullback.lift x y (by rw [hx, hy])
@[reassoc] theorem nativeCubePoint_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    nativeCubePoint f g x hx y hy ≫ (pullback.fst f g ≫ f) = 𝟙 _ := by
  simp [nativeCubePoint, hx]

theorem nativeCubePoint_eq_faceX
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    x ≫ nativeCubeFaceXBase f g y hy = nativeCubePoint f g x hx y hy := by
  apply pullback.hom_ext
  · simp [nativeCubeFaceXBase, nativeCubePoint, Category.assoc]
  · simp only [nativeCubeFaceXBase, nativeCubePoint, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, hx, Category.id_comp]

def nativeCubeSectionXR (f : X ⟶ Spec (.of k)) (a : Z ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) : Z ⟶ pullback f a :=
  pullback.lift (a ≫ x) (𝟙 Z) (by simp [Category.assoc, hx])
def nativeCubeZeroSectionR (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) : Z ⟶ pullback (pullback.fst f g ≫ f) a :=
  pullback.lift (a ≫ nativeCubePoint f g x hx y hy) (𝟙 Z)
    (by simp [Category.assoc, nativeCubePoint_struct])

theorem nativeCubeSectionXR_comp_faceXR
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (a : Z ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    nativeCubeSectionXR f a x hx ≫ nativeCubeFaceXR f g a y hy =
      nativeCubeZeroSectionR f g a x hx y hy := by
  apply pullback.hom_ext
  · simp [nativeCubeSectionXR, nativeCubeFaceXR, nativeCubeZeroSectionR, Category.assoc]
    simpa only [Category.assoc] using
      congrArg (fun m => a ≫ m) (nativeCubePoint_eq_faceX f g x hx y hy)
  · simp [nativeCubeSectionXR, nativeCubeFaceXR, nativeCubeZeroSectionR]

/-- The actual normalized-seesaw section is this literal native zero section. -/
theorem nativeCubeZeroSectionR_eq_sectionBaseChange
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (a : Z ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    nativeCubeZeroSectionR f g a x hx y hy =
      sectionBaseChange (pullback.fst f g ≫ f)
        (nativeCubePoint f g x hx y hy) (nativeCubePoint_struct f g x hx y hy) (Over.mk a) := by
  rfl

/-- Normalization is PROVED from one actual entire face, with no extra
normalization/model premise in the intended reduced opening theorem. -/
theorem nativeCube_normalized_of_faceX
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (a : Z ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (L : (pullback (pullback.fst f g ≫ f) a).Pic)
    (hFace : Scheme.Pic.map (nativeCubeFaceXR f g a y hy) L = 1) :
    Scheme.Pic.map (sectionBaseChange (pullback.fst f g ≫ f)
      (nativeCubePoint f g x hx y hy) (nativeCubePoint_struct f g x hx y hy) (Over.mk a)) L = 1 := by
  rw [← nativeCubeZeroSectionR_eq_sectionBaseChange f g a x hx y hy,
    ← nativeCubeSectionXR_comp_faceXR f g a x hx y hy,
    Scheme.Pic.map_comp, hFace, Scheme.Pic.map_one]

end ZInQ.Contrib.CloudR2Poincare.L6
