/-
H5 lane3 Step 1: `TensorHomNeZero` (SectionsBothWays.lean) PROVED from published fork W07.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

1. `mono_of_ne_zero_unitHom`: on an integral scheme, a nonzero `θ : 𝟙_ ⟶ L` into an invertible
   module is a monomorphism.
   * Put `ψ := θ ▷ Lᵛ ≫ (L ⊗ Lᵛ ≅ 𝟙_)`. It is nonzero, because `tensorRight Lᵛ` is faithful.
   * W07 `Hom.isInvertible_zeroLocus` (integral) makes `Z(ψ)` an effective Cartier divisor.
   * W07 `Hom.exists_iso_toModules_zeroLocus` factors `ψ` as an iso followed by the ideal
     inclusion, so `ψ` is mono.
   * Then `θ ▷ Lᵛ` is mono, and `θ` is mono, since the equivalence `tensorRight Lᵛ` reflects
     monomorphisms.
2. `tensorHomNeZero`: write `θ ⊗ φ = θ ▷ 𝟙 ≫ L ◁ φ`, a composite of monos (equivalences preserve
   monos). If it were `0`, then `𝟙_ ⊗ 𝟙_`, hence `𝟙_`, would be a zero object, forcing `θ = 0`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.SectionsBothWays
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocus
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorEquivalence

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem mono_of_ne_zero_unitHom {X : Scheme.{u}} [IsIntegral X] {L : X.Modules} [L.IsInvertible]
    (θ : 𝟙_ X.Modules ⟶ L) (hθ : θ ≠ 0) : Mono θ := by
  let ψ : 𝟙_ X.Modules ⊗ Scheme.Modules.dual L ⟶ 𝟙_ X.Modules :=
    θ ▷ Scheme.Modules.dual L ≫ (Scheme.Modules.tensorObjDualIsoUnit L).hom
  have hψ : ψ ≠ 0 := by
    intro h0
    apply hθ
    have h1 : θ ▷ Scheme.Modules.dual L = 0 := by
      simpa [ψ] using congrArg (· ≫ (Scheme.Modules.tensorObjDualIsoUnit L).inv) h0
    apply (tensorRight (Scheme.Modules.dual L)).map_injective
    rw [Functor.map_zero]
    exact h1
  have hD : ψ.zeroLocus.IsInvertible := Scheme.Modules.Hom.isInvertible_zeroLocus hψ
  obtain ⟨κ, hκ⟩ := Scheme.Modules.Hom.exists_iso_toModules_zeroLocus ψ hD
  have hmψ : Mono ψ := by
    have h : Mono (κ.hom ≫ ψ.zeroLocus.toModulesι) := inferInstance
    rwa [hκ] at h
  haveI : Mono (θ ▷ Scheme.Modules.dual L) :=
    @mono_of_mono _ _ _ _ _ _ (Scheme.Modules.tensorObjDualIsoUnit L).hom hmψ
  exact (tensorRight (Scheme.Modules.dual L)).mono_of_mono_map ‹_›

/-- `TensorHomNeZero`, PROVED. -/
theorem tensorHomNeZero : TensorHomNeZero.{u} := by
  intro X _ L M _ _ θ φ hθ hφ h0
  haveI := mono_of_ne_zero_unitHom θ hθ
  haveI := mono_of_ne_zero_unitHom φ hφ
  haveI : Mono (θ ▷ 𝟙_ X.Modules) :=
    (inferInstance : Mono ((tensorRight (𝟙_ X.Modules)).map θ))
  haveI : Mono (L ◁ φ) := (inferInstance : Mono ((tensorLeft L).map φ))
  have hm : Mono (θ ⊗ₘ φ) := by
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  rw [h0] at hm
  have hid : 𝟙 (𝟙_ X.Modules ⊗ 𝟙_ X.Modules) = 0 :=
    (@cancel_mono _ _ _ _ _ (0 : 𝟙_ X.Modules ⊗ 𝟙_ X.Modules ⟶ L ⊗ M) hm _ _).mp (by simp)
  have hz : IsZero (𝟙_ X.Modules ⊗ 𝟙_ X.Modules) := (IsZero.iff_id_eq_zero _).mpr hid
  exact hθ ((hz.of_iso (λ_ (𝟙_ X.Modules)).symm).eq_of_src θ 0)

/-- R3 with its sub-gaps discharged: from I5b alone. -/
theorem sectionsVanishFromInversion_proved : SectionsVanishFromInversion.{u} :=
  sectionsVanishFromInversion (trivialOfSectionsBothWays tensorHomNeZero)

end ZInQ.Contrib.CloudR2NOS.Step1
