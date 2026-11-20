import ZInQKernel.Contrib.CloudR2Poincare.L2.HOneFaceSurjection
import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeHOneProduct

/-!
# Injectivity of the ACTUAL native H¹ two-face map

The real k-linear face map is already split-surjective. The actual native
Leray/field-BC dimension bound and proper cohomology finiteness force its
kernel to vanish. No Kunneth, face-injectivity, rank or cube premise is supplied.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L6

section DefaultRankBound

variable {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    [Module.Finite K V] [Module.Finite K W]

private theorem default_linear_injective_of_surjective_finrank_le
    (F : V →ₗ[K] W) (hsur : Function.Surjective F)
    (hdim : Module.finrank K V ≤ Module.finrank K W) : Function.Injective F := by
  have hR : Module.finrank K (LinearMap.range F) = Module.finrank K W := by
    rw [LinearMap.range_eq_top.mpr hsur]
    exact Submodule.topEquiv.finrank_eq
  have hr : Module.finrank K (LinearMap.range F) + Module.finrank K (LinearMap.ker F) =
      Module.finrank K V := by
    have h := (LinearMap.ker F).finrank_quotient_add_finrank
    rwa [F.quotKerEquivRange.finrank_eq] at h
  have hk : Module.finrank K (LinearMap.ker F) = 0 := by
    rw [hR] at hr
    omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

end DefaultRankBound

/-- EXACT native H¹ two-face injectivity over every field, for proper geometrically
integral factors with actual rational points, using the literal native H-pullback pair. -/
theorem nativeHOne_twoFaces_injective
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    Function.Injective
      (fun z : (Scheme.Modules.unit (X ⊗ Y).left).H 1 =>
        (nativeUnitHPullback (lift (𝟙 X) (toUnit X ≫ y)).left 1 z,
          nativeUnitHPullback (lift (toUnit Y ≫ x) (𝟙 Y)).left 1 z)) := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  letI : (X ⊗ Y).left.Over (Spec (.of k)) := ⟨(X ⊗ Y).hom⟩
  haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
  haveI : IsProper (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsProper Y.hom)
  haveI : IsProper (fst X Y).left := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom))
  haveI : IsProper (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y)]
    infer_instance
  haveI : IsProper ((X ⊗ Y).left ↘ Spec (.of k)) := inferInstanceAs (IsProper (X ⊗ Y).hom)
  haveI : Module.Finite k ((Scheme.Modules.unit X.left).H 1) :=
    ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.finite_unit_H 1
  haveI : Module.Finite k ((Scheme.Modules.unit Y.left).H 1) :=
    ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.finite_unit_H 1
  haveI : Module.Finite k ((Scheme.Modules.unit (X ⊗ Y).left).H 1) :=
    ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients.finite_unit_H 1
  let F := ZInQ.Contrib.CloudR2Poincare.L2.nativeHOne_twoFacesLinearMap X Y x y
  have hsur : Function.Surjective F :=
    ZInQ.Contrib.CloudR2Poincare.L2.nativeHOne_twoFacesLinearMap_surjective X Y x y
  have hdim : Module.finrank k ((Scheme.Modules.unit (X ⊗ Y).left).H 1) ≤
      Module.finrank k ((Scheme.Modules.unit X.left).H 1 × (Scheme.Modules.unit Y.left).H 1) := by
    simpa only [Module.finrank_prod] using
      ZInQ.Contrib.CloudR2Poincare.L3.nativeHOne_product_dim_le X Y
  exact default_linear_injective_of_surjective_finrank_le F hsur hdim

end ZInQ.Contrib.CloudR2Poincare.L6
