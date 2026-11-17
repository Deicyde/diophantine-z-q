import ZInQKernel.Contrib.CloudR2Poincare.L4.CubeFaces.Geometry

/-!
# Actual cube family geometry and same-base face triangles

These ordinary proofs use only the exposed L6 face definitions and native
proper/flat/geometrically-integral base change. No Čech model, affine-face,
normalization or cohomology premise is supplied. In particular, both face
families are literally the pullbacks of f and g, not replacement schemes.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L4.CubeFaces

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}

/-- Actual proper/flat/geometrically-integral product over the original field. -/
theorem nativeCubeProduct_geometry
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g] :
    IsProper (pullback.fst f g ≫ f) ∧ Flat (pullback.fst f g ≫ f) ∧
      GeometricallyIntegral (pullback.fst f g ≫ f) := by
  haveI : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  haveI : GeometricallyIntegral (Over.mk f).hom := inferInstanceAs (GeometricallyIntegral f)
  haveI : IsProper (Over.mk g).hom := inferInstanceAs (IsProper g)
  haveI : GeometricallyIntegral (Over.mk g).hom := inferInstanceAs (GeometricallyIntegral g)
  have hgi := L6.nativeProduct_geometricallyIntegral (Over.mk f) (Over.mk g)
  change GeometricallyIntegral (pullback.fst f g ≫ f) at hgi
  exact ⟨inferInstance, inferInstance, hgi⟩

/-- The actual parameterized cube family is proper, flat and geometrically integral. -/
theorem nativeCubeFamily_geometry
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    (a : Z ⟶ Spec (.of k)) :
    IsProper (pullback.snd (pullback.fst f g ≫ f) a) ∧
      Flat (pullback.snd (pullback.fst f g ≫ f) a) ∧
      GeometricallyIntegral (pullback.snd (pullback.fst f g ≫ f) a) := by
  obtain ⟨hp, hf, hi⟩ := nativeCubeProduct_geometry f g
  haveI := hp
  haveI := hf
  haveI := hi
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Structure triangle for the SAME literal X-family face. -/
theorem nativeCubeFaceXR_structure
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceXR f g a y hy ≫ pullback.snd (pullback.fst f g ≫ f) a =
      pullback.snd f a := L6.nativeCubeFaceXR_struct f g a y hy

/-- Structure triangle for the SAME literal Y-family face. -/
theorem nativeCubeFaceYR_structure
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    L6.nativeCubeFaceYR f g a x hx ≫ pullback.snd (pullback.fst f g ≫ f) a =
      pullback.snd g a := L6.nativeCubeFaceYR_struct f g a x hx

/-- The actual X-face family is proper and flat, with no extra face-model input. -/
theorem nativeCubeFaceXR_family_geometry
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    IsProper (L6.nativeCubeFaceXR f g a y hy ≫ pullback.snd (pullback.fst f g ≫ f) a) ∧
      Flat (L6.nativeCubeFaceXR f g a y hy ≫ pullback.snd (pullback.fst f g ≫ f) a) := by
  rw [nativeCubeFaceXR_structure]
  exact ⟨inferInstance, inferInstance⟩

/-- The actual Y-face family is proper and flat, with no extra face-model input. -/
theorem nativeCubeFaceYR_family_geometry
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper g] [GeometricallyIntegral g]
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    IsProper (L6.nativeCubeFaceYR f g a x hx ≫ pullback.snd (pullback.fst f g ≫ f) a) ∧
      Flat (L6.nativeCubeFaceYR f g a x hx ≫ pullback.snd (pullback.fst f g ≫ f) a) := by
  rw [nativeCubeFaceYR_structure]
  exact ⟨inferInstance, inferInstance⟩

/-- Literal left-projection commutation used by scalar-base-change face squares. -/
theorem nativeCubeFaceXR_base_comm
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceXR f g a y hy ≫ pullback.fst (pullback.fst f g ≫ f) a =
      pullback.fst f a ≫ L6.nativeCubeFaceXBase f g y hy := by
  simp [L6.nativeCubeFaceXR]

/-- Literal left-projection commutation used by scalar-base-change face squares. -/
theorem nativeCubeFaceYR_base_comm
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    L6.nativeCubeFaceYR f g a x hx ≫ pullback.fst (pullback.fst f g ≫ f) a =
      pullback.fst g a ≫ L6.nativeCubeFaceYBase f g x hx := by
  simp [L6.nativeCubeFaceYR]

/-- The source X-face family is literally the pullback of f to the parameter. -/
theorem nativeCubeXFamily_isPullback (f : X ⟶ Spec (.of k)) (a : Z ⟶ Spec (.of k)) :
    IsPullback (pullback.fst f a) (pullback.snd f a) f a := IsPullback.of_hasPullback f a

/-- The source Y-face family is literally the pullback of g to the parameter. -/
theorem nativeCubeYFamily_isPullback (g : Y ⟶ Spec (.of k)) (a : Z ⟶ Spec (.of k)) :
    IsPullback (pullback.fst g a) (pullback.snd g a) g a := IsPullback.of_hasPullback g a

/-- The target cube family is literally the pullback of the original product to the parameter. -/
theorem nativeCubeFamily_isPullback
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (a : Z ⟶ Spec (.of k)) :
    IsPullback (pullback.fst (pullback.fst f g ≫ f) a)
      (pullback.snd (pullback.fst f g ≫ f) a) (pullback.fst f g ≫ f) a :=
  IsPullback.of_hasPullback (pullback.fst f g ≫ f) a

end ZInQ.Contrib.CloudR2Poincare.L4.CubeFaces
