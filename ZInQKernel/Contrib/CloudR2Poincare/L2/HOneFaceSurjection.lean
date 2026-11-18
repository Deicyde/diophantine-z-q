import ZInQKernel.Contrib.CloudR2Poincare.L6.HPullbackBasic
import ZInQKernel.Contrib.CloudR2Poincare.L6.HPullbackCoherence
import ZInQKernel.Contrib.CloudR2Poincare.L4.HPullback.Coherence
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Affine.Vanishing
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.LinearAlgebra.Prod

/-!
# Actual H¹ two-face split surjection

The face arrows and projection arrows are the original morphisms in Over k.
Every pullback is L6's existing native structure-sheaf cohomology pullback.
Its composition/identity/scalar coherences are imported suppliers, not
reproved, assumed or replaced by numerical comparisons. The cross composites
factor through the actual Spec k and its native H¹(O) vanishes by affine
quasi-coherent cohomology. The explicit section is p₁* a + p₂* b.

No properness, geometric-integrality, characteristic-zero, finite-dimensional,
Künneth, H¹(X,O)-vanishing, rank or face-isomorphism hypothesis is needed for
this split SURJECTION. No injection or native cube/square theorem is claimed.
Compilation waits for L6's genuine comp/id certification; source alone is not
a certificate of those supplied laws.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- The X-face followed by p₁ gives identity on actual native H¹(X,O). -/
theorem nativeHOne_faceX_fst
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (a : (Scheme.Modules.unit X.left).H 1) :
    L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1
      (L6.nativeUnitHPullback (fst X Y).left 1 a) = a := by
  have hf : (lift (𝟙 X) (toUnit X ≫ y)).left ≫ (fst X Y).left = 𝟙 X.left := by
    have h : lift (𝟙 X) (toUnit X ≫ y) ≫ fst X Y = (𝟙 X : X ⟶ X) := by simp
    simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left h
  change ((L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1).comp
    (L6.nativeUnitHPullback (fst X Y).left 1)) a = a
  rw [← L6.nativeUnitHPullback_comp, hf, L6.nativeUnitHPullback_id]
  rfl

/-- The Y-face followed by p₂ gives identity on actual native H¹(Y,O). -/
theorem nativeHOne_faceY_snd
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (b : (Scheme.Modules.unit Y.left).H 1) :
    L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1
      (L6.nativeUnitHPullback (snd X Y).left 1 b) = b := by
  have hf : (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫ (snd X Y).left = 𝟙 Y.left := by
    have h : lift (toUnit Y ≫ x) (𝟙 Y) ≫ snd X Y = (𝟙 Y : Y ⟶ Y) := by simp
    simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left h
  change ((L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1).comp
    (L6.nativeUnitHPullback (snd X Y).left 1)) b = b
  rw [← L6.nativeUnitHPullback_comp, hf, L6.nativeUnitHPullback_id]
  rfl

/-- The X-face/p₂ cross composite vanishes through the actual field spectrum. -/
theorem nativeHOne_faceX_snd_eq_zero
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (b : (Scheme.Modules.unit Y.left).H 1) :
    L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1
      (L6.nativeUnitHPullback (snd X Y).left 1 b) = 0 := by
  have hf : (lift (𝟙 X) (toUnit X ≫ y)).left ≫ (snd X Y).left =
      (toUnit X).left ≫ y.left := by
    change (lift (𝟙 X) (toUnit X ≫ y) ≫ snd X Y).left = (toUnit X ≫ y).left
    rw [lift_snd]
  letI : Subsingleton ((Scheme.Modules.unit (𝟙_ (Over (Spec (.of k)))).left).H 1) := by
    rw [Over.tensorUnit_left]
    exact Scheme.Modules.subsingleton_H_succ_of_isAffine (Scheme.Modules.unit (Spec (.of k))) 0
  have hz : L6.nativeUnitHPullback y.left 1 b = 0 := Subsingleton.elim _ _
  change ((L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1).comp
    (L6.nativeUnitHPullback (snd X Y).left 1)) b = 0
  rw [← L6.nativeUnitHPullback_comp, hf, L6.nativeUnitHPullback_comp]
  change L6.nativeUnitHPullback (toUnit X).left 1 (L6.nativeUnitHPullback y.left 1 b) = 0
  rw [hz, map_zero]

/-- The Y-face/p₁ cross composite vanishes through the actual field spectrum. -/
theorem nativeHOne_faceY_fst_eq_zero
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (a : (Scheme.Modules.unit X.left).H 1) :
    L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1
      (L6.nativeUnitHPullback (fst X Y).left 1 a) = 0 := by
  have hf : (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫ (fst X Y).left =
      (toUnit Y).left ≫ x.left := by
    change (lift (toUnit Y ≫ x) (𝟙 Y) ≫ fst X Y).left = (toUnit Y ≫ x).left
    rw [lift_fst]
  letI : Subsingleton ((Scheme.Modules.unit (𝟙_ (Over (Spec (.of k)))).left).H 1) := by
    rw [Over.tensorUnit_left]
    exact Scheme.Modules.subsingleton_H_succ_of_isAffine (Scheme.Modules.unit (Spec (.of k))) 0
  have hz : L6.nativeUnitHPullback x.left 1 a = 0 := Subsingleton.elim _ _
  change ((L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1).comp
    (L6.nativeUnitHPullback (fst X Y).left 1)) a = 0
  rw [← L6.nativeUnitHPullback_comp, hf, L6.nativeUnitHPullback_comp]
  change L6.nativeUnitHPullback (toUnit Y).left 1 (L6.nativeUnitHPullback x.left 1 a) = 0
  rw [hz, map_zero]

/-- The ACTUAL right inverse of the literal two-face native H¹ map. -/
theorem nativeHOne_twoFaces_rightInverse
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    Function.RightInverse
      (fun ab : (Scheme.Modules.unit X.left).H 1 × (Scheme.Modules.unit Y.left).H 1 =>
        L6.nativeUnitHPullback (fst X Y).left 1 ab.1 +
          L6.nativeUnitHPullback (snd X Y).left 1 ab.2)
      (fun z : (Scheme.Modules.unit (X ⊗ Y).left).H 1 =>
        (L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1 z,
          L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1 z)) := by
  intro ab
  apply Prod.ext
  · change L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1
      (L6.nativeUnitHPullback (fst X Y).left 1 ab.1 +
        L6.nativeUnitHPullback (snd X Y).left 1 ab.2) = ab.1
    rw [map_add, nativeHOne_faceX_fst, nativeHOne_faceX_snd_eq_zero, add_zero]
  · change L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1
      (L6.nativeUnitHPullback (fst X Y).left 1 ab.1 +
        L6.nativeUnitHPullback (snd X Y).left 1 ab.2) = ab.2
    rw [map_add, nativeHOne_faceY_fst_eq_zero, nativeHOne_faceY_snd, zero_add]

/-- Surjection of the EXACT raw pair required by L6's H¹ injection consumer. -/
theorem nativeHOne_twoFaces_surjective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    Function.Surjective
      (fun z : (Scheme.Modules.unit (X ⊗ Y).left).H 1 =>
        (L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1 z,
          L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1 z)) :=
  (nativeHOne_twoFaces_rightInverse X Y x y).surjective

/-- The literal native two-face map, genuinely linear over the ORIGINAL field. -/
def nativeHOne_twoFacesLinearMap
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    (Scheme.Modules.unit (X ⊗ Y).left).H 1 →ₗ[k]
      (Scheme.Modules.unit X.left).H 1 × (Scheme.Modules.unit Y.left).H 1 := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
  exact (L6.nativeUnitHPullbackLinearMap X (X ⊗ Y) (lift (𝟙 X) (toUnit X ≫ y)) 1).prod
    (L6.nativeUnitHPullbackLinearMap Y (X ⊗ Y) (lift (toUnit Y ≫ x) (𝟙 Y)) 1)

/-- Definitional identification with L6's original raw H¹ face-pair map. -/
theorem nativeHOne_twoFacesLinearMap_apply
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    ∀ z : (Scheme.Modules.unit (X ⊗ Y).left).H 1,
      nativeHOne_twoFacesLinearMap X Y x y z =
        (L6.nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1 z,
          L6.nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1 z) := by
  intros
  rfl

/-- The explicit projection-sum section, linear over the ORIGINAL field. -/
def nativeHOne_projectionSectionLinearMap
    {k : Type u} [Field k] (X Y : Over (Spec (.of k))) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    (Scheme.Modules.unit X.left).H 1 × (Scheme.Modules.unit Y.left).H 1 →ₗ[k]
      (Scheme.Modules.unit (X ⊗ Y).left).H 1 := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
  exact (L6.nativeUnitHPullbackLinearMap (X ⊗ Y) X (fst X Y) 1).coprod
    (L6.nativeUnitHPullbackLinearMap (X ⊗ Y) Y (snd X Y) 1)

/-- The section is definitionally p₁* a + p₂* b, not a rank-selected inverse. -/
theorem nativeHOne_projectionSectionLinearMap_apply
    {k : Type u} [Field k] (X Y : Over (Spec (.of k))) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    ∀ ab : (Scheme.Modules.unit X.left).H 1 × (Scheme.Modules.unit Y.left).H 1,
      nativeHOne_projectionSectionLinearMap X Y ab =
        L6.nativeUnitHPullback (fst X Y).left 1 ab.1 +
          L6.nativeUnitHPullback (snd X Y).left 1 ab.2 := by
  intros
  rfl

/-- The actual field-linear face map composed with the actual section is id. -/
theorem nativeHOne_twoFacesLinearMap_comp_section
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    (nativeHOne_twoFacesLinearMap X Y x y).comp (nativeHOne_projectionSectionLinearMap X Y) =
      LinearMap.id := by
  apply LinearMap.ext
  intro ab
  exact nativeHOne_twoFaces_rightInverse X Y x y ab

/-- Surjectivity of the ACTUAL k-linear map used in the dimension argument. -/
theorem nativeHOne_twoFacesLinearMap_surjective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
    letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
    Function.Surjective (nativeHOne_twoFacesLinearMap X Y x y) := by
  intros
  exact nativeHOne_twoFaces_surjective X Y x y

end ZInQ.Contrib.CloudR2Poincare.L2
