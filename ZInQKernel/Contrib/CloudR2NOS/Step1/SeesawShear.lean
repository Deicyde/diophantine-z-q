/-
H5 FIX EDITION STEP-F2 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/SeesawShear.lean (sha256 274394acdc89fe5c70ffe2a6b5309920e8b48808540bea4bc99c5c326a0929b2).
Body change relative to the base: ONLY P5, the line `open CategoryTheory.CartesianMonoidalCategory` inserted before `namespace` (record step-fix2/FIX_RECORD_STEP_F2.json). Any header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: SS `SeesawShearFromSeesaw` and `LineOnSpecFieldTrivial` (adapter). 2026-11-17.
v2, interface v2: `Y` carries the internal `[IsProperIntegralGroup Y]`. v1 47635d96 is in
history/.
New file. SOURCE-ONLY, UNCOMPILED. Universe u, any characteristic.

* `lineOnSpecFieldTrivial` is C2's held-Source `nonempty_iso_unit_on_spec_field`
  (lane2 NativeCubeUnitReduction.lean 42829185…), cited and not duplicated.
* `seesawShear_of` is PROVED from GM1 and that adapter.
  - The shear is `S := lift (fst * (snd ≫ j)) snd`, defined in `Over (Spec K)` with the SAME group
    law and the monoid hom `j`. Its inverse is `lift (fst * (snd ≫ j)⁻¹) snd`, by Mathlib Hom-group
    identities.
  - `ψ := S.left` is an automorphism of `A ×_K Y` over `Y`.
  - Apply GM1 to `Λ := (ψ ≫ pr₁)^*L ⊗ (pr₁^*L)ᵛ`. Its rational slices are `t_{t j}^*L ⊗ Lᵛ ≅ O`.
    Its base section is `j^*L ⊗ ((fT ≫ x₀)^*L)ᵛ ≅ j^*L`.
  - So `ψ^*pr₁^*L ≅ pr₁^*L ⊗ pr₂^*(j^*L)`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Seesaw
import ZInQKernel.Contrib.CloudR2NOS.Step1.PicZeroSections
import NativeCubeUnitReduction

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

open CategoryTheory.CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- C2's held-Source theorem, adapted (`unit` and `𝟙_` agree definitionally). -/
theorem lineOnSpecFieldTrivial : LineOnSpecFieldTrivial.{u} := fun M _ =>
  H5OriginalDVR.Lane2.NativeCubeUnitReduction.nonempty_iso_unit_on_spec_field M

section Shear

variable {K : Type u} [Field K] (A Y : Grp (Over (Spec (CommRingCat.of K)))) (j : Y.X ⟶ A.X)

/-- The shear `(a, y) ↦ (a · j y, y)` as a morphism of `Over (Spec K)`. -/
abbrev shearOver : A.X ⊗ Y.X ⟶ A.X ⊗ Y.X := lift (fst A.X Y.X * (snd A.X Y.X ≫ j)) (snd A.X Y.X)

/-- Its inverse `(a, y) ↦ (a · (j y)⁻¹, y)`. -/
abbrev shearInvOver : A.X ⊗ Y.X ⟶ A.X ⊗ Y.X :=
  lift (fst A.X Y.X * (snd A.X Y.X ≫ j)⁻¹) (snd A.X Y.X)

theorem shearOver_hom_inv : shearOver A Y j ≫ shearInvOver A Y j = 𝟙 _ := by
  rw [comp_lift, MonObj.comp_mul, lift_fst, GrpObj.comp_inv, lift_snd_assoc, lift_snd,
    mul_inv_cancel_right, lift_fst_snd]

theorem shearOver_inv_hom : shearInvOver A Y j ≫ shearOver A Y j = 𝟙 _ := by
  rw [comp_lift, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd, inv_mul_cancel_right,
    lift_fst_snd]

instance isIso_shearOver : IsIso (shearOver A Y j) :=
  ⟨⟨shearInvOver A Y j, shearOver_hom_inv A Y j, shearOver_inv_hom A Y j⟩⟩

end Shear

/-- SS, PROVED from GM1 and `LineOnSpecFieldTrivial`. -/
theorem seesawShear_of (hGM1 : SeesawPulledBack.{u}) (hF : LineOnSpecFieldTrivial.{u}) :
    SeesawShear.{u} := by
  intro K _ _ A Y _ _ j _ hjc L _ htr
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsProper Y.X.hom := IsProperIntegralGroup.proper
  haveI : IsIntegral Y.X.left := isIntegral_of_isProperIntegralGroup Y
  -- the shear on the underlying product scheme
  let ψ : Limits.pullback A.X.hom Y.X.hom ⟶ Limits.pullback A.X.hom Y.X.hom := (shearOver A Y j).left
  haveI : IsIso ψ := (inferInstance : IsIso ((Over.forget _).map (shearOver A Y j)))
  have hψ : ψ ≫ pullback.snd A.X.hom Y.X.hom = pullback.snd A.X.hom Y.X.hom :=
    congrArg CommaMorphism.left (lift_snd (fst A.X Y.X * (snd A.X Y.X ≫ j)) (snd A.X Y.X))
  -- `m' := ψ ≫ pr₁ = (fst * (snd ≫ j)).left`
  let m' : Limits.pullback A.X.hom Y.X.hom ⟶ A.X.left := (fst A.X Y.X * (snd A.X Y.X ≫ j)).left
  have hm' : ψ ≫ pullback.fst A.X.hom Y.X.hom = m' :=
    congrArg CommaMorphism.left (lift_fst (fst A.X Y.X * (snd A.X Y.X ≫ j)) (snd A.X Y.X))
  let x₀ : Spec (CommRingCat.of K) ⟶ A.X.left := (η[A.X] : Pt K ⟶ A.X).left
  have hx₀ : x₀ ≫ A.X.hom = 𝟙 _ := Over.w (η[A.X] : Pt K ⟶ A.X)
  -- the normalized line `Λ = m'^*L ⊗ (pr₁^*L)ᵛ`; its rational slices are trivial
  have hslice : ∀ (t : Spec (CommRingCat.of K) ⟶ Y.X.left) (ht : t ≫ Y.X.hom = 𝟙 _),
      Iso' ((Scheme.Modules.pullback (sliceAt A.X.hom Y.X.hom t ht)).obj
        ((Scheme.Modules.pullback m').obj L ⊗
          Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.fst A.X.hom Y.X.hom)).obj L)))
        (𝟙_ A.X.left.Modules) := by
    intro t ht
    let t' : Pt K ⟶ Y.X := Over.homMk t ht
    have h1 : sliceAt A.X.hom Y.X.hom t ht ≫ m' = transl A (t' ≫ j) := by
      have : lift (𝟙 A.X) (toUnit A.X ≫ t') ≫ (fst A.X Y.X * (snd A.X Y.X ≫ j)) =
          lift (𝟙 A.X) (toUnit A.X ≫ (t' ≫ j)) ≫ μ[A.X] := by
        rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, ← MonObj.Hom.mul_def, Category.assoc]
      exact congrArg CommaMorphism.left this
    have h2 : sliceAt A.X.hom Y.X.hom t ht ≫ pullback.fst A.X.hom Y.X.hom = 𝟙 _ :=
      pullback.lift_fst _ _ _
    refine (iso'_pb_tensor _ _ _).trans ?_
    refine (((iso'_pb_comp _ _ _).trans ((iso'_pb_congr h1 _).trans (htr t'))).tensor
      ((iso'_pb_dual _ _).trans
        ((iso'_pb_comp _ _ _).trans ((iso'_pb_congr h2 _).trans (iso'_pb_id _))).dual)).trans ?_
    exact iso'_dual L
  -- GM1
  obtain ⟨eΛ⟩ := hGM1 A.X.hom Y.X.hom x₀ hx₀ _ hslice
  -- the base section restriction of `Λ` is `j^*L`
  have hb1 : baseSection A.X.hom Y.X.hom x₀ hx₀ ≫ m' = j.left := by
    have : lift (toUnit Y.X ≫ η[A.X]) (𝟙 Y.X) ≫ (fst A.X Y.X * (snd A.X Y.X ≫ j)) = j := by
      rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, Category.id_comp, ← MonObj.Hom.one_def,
        one_mul]
    exact congrArg CommaMorphism.left this
  have hb2 : baseSection A.X.hom Y.X.hom x₀ hx₀ ≫ pullback.fst A.X.hom Y.X.hom = Y.X.hom ≫ x₀ :=
    pullback.lift_fst _ _ _
  have hbase : Iso' ((Scheme.Modules.pullback (baseSection A.X.hom Y.X.hom x₀ hx₀)).obj
      ((Scheme.Modules.pullback m').obj L ⊗
        Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.fst A.X.hom Y.X.hom)).obj L)))
      ((Scheme.Modules.pullback j.left).obj L) := by
    refine (iso'_pb_tensor _ _ _).trans ?_
    refine (((iso'_pb_comp _ _ _).trans (iso'_pb_congr hb1 _)).tensor
      ((iso'_pb_dual _ _).trans
        ((iso'_pb_comp _ _ _).trans <| (iso'_pb_congr hb2 _).trans <|
          (iso'_pb_comp _ _ _).symm.trans <| (Iso'.pb _ (hF _)).trans (iso'_pb_unit _)).dual)).trans ?_
    exact ((iso'_refl _).tensor (iso'_dual_unit _)).trans (iso'_unit_right _)
  refine ⟨ψ, inferInstance, hψ, ?_⟩
  -- `ψ^*pr₁^*L ≅ m'^*L ≅ Λ ⊗ pr₁^*L ≅ pr₂^*(j^*L) ⊗ pr₁^*L ≅ pr₁^*L ⊗ pr₂^*(j^*L)`
  have hΛ : Iso' ((Scheme.Modules.pullback m').obj L)
      (((Scheme.Modules.pullback m').obj L ⊗
          Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.fst A.X.hom Y.X.hom)).obj L)) ⊗
        (Scheme.Modules.pullback (pullback.fst A.X.hom Y.X.hom)).obj L) :=
    (iso'_unit_right _).symm.trans <|
      ((iso'_refl _).tensor ((iso'_comm _ _).trans (iso'_dual _)).symm).trans
        (iso'_assoc _ _ _).symm
  exact ((iso'_pb_comp _ _ _).trans <| (iso'_pb_congr hm' _).trans <| hΛ.trans <|
    ((Nonempty.intro eΛ).tensor (iso'_refl _)).trans <|
      (((hbase.pb _)).tensor (iso'_refl _)).trans (iso'_comm _ _))

/-- SS as the named implication of Interfaces.lean (given C2's field-line triviality). -/
theorem seesawShearFromSeesaw : SeesawShearFromSeesaw.{u} := fun hGM1 =>
  seesawShear_of hGM1 lineOnSpecFieldTrivial

end ZInQ.Contrib.CloudR2NOS.Step1
