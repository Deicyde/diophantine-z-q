/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_gluing_openCover_of_bijective_sections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_bijective_sections

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra Opposite

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  classical
  have hJ : Scheme.zariskiTopology.over (Spec (CommRingCat.of R)) =
      (Scheme.overPretopology @IsOpenImmersion (Spec (CommRingCat.of R))).toGrothendieck :=
    Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopology _ _
  rw [hJ, Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  intro Y E
  let 𝒰 : Y.left.Cover (Scheme.precoverage @IsOpenImmersion) :=
    E.map (Over.forget (Spec (CommRingCat.of R))) le_rfl
  letI : Y.left.Over (Spec (CommRingCat.of R)) := ⟨Y.hom⟩
  letI (i : E.I₀) : (𝒰.X i).Over (Spec (CommRingCat.of R)) := ⟨(E.X i).hom⟩
  letI : 𝒰.Over (Spec (CommRingCat.of R)) :=
    { «over» i := inferInstance
      isOver_map i := ⟨Over.w (E.f i)⟩ }
  change Presieve.IsSheafFor _ (𝒰.toPresieveOver)
  rw [Scheme.Cover.toPresieveOver, Presieve.isSheafFor_arrows_iff]
  intro x hx

  let u : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ Spec (CommRingCat.of R) := fun i =>
    ((𝒰.X i).asOver (Spec (CommRingCat.of R))).hom
  let f : ∀ i, SchemeHomOver (u i) Y.hom := fun i =>
    ⟨((𝒰.f i).asOver (Spec (CommRingCat.of R))).left, Over.w ((𝒰.f i).asOver (Spec (CommRingCat.of R)))⟩
  haveI hfo : ∀ i, IsOpenImmersion (f i).1 := fun i => 𝒰.map_prop i
  have hf : ∀ y : Y.left, ∃ i, y ∈ Set.range (f i).1.base := fun y => by
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq y
    exact ⟨i, z, hz⟩

  let M : ∀ i, RigidifiedLineBundle c ε (u i) := fun i => (x i).1.out
  have hM : ∀ i, Quotient.mk _ (M i) = (x i).1 := fun i => Quotient.out_eq _
  have hMP : ∀ i, FibrewiseAlgEquivZero (M i) := fun i => by
    have h : (algEquivZeroCut c ε).onClasses _ (x i).1 := (x i).2
    rw [← hM i] at h
    exact h

  have hcompat : ∀ (i j : 𝒰.I₀) (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ : SchemeHomOver z (u i)) (p₂ : SchemeHomOver z (u j)),
      p₁.1 ≫ (f i).1 = p₂.1 ≫ (f j).1 → Nonempty (((M i).pullbackAlong p₁).L ≅ ((M j).pullbackAlong p₂).L) := by
    intro i j Z z p₁ p₂ hp
    let P₁ : Over.mk z ⟶ (𝒰.X i).asOver (Spec (CommRingCat.of R)) := Over.homMk p₁.1 p₁.2
    let P₂ : Over.mk z ⟶ (𝒰.X j).asOver (Spec (CommRingCat.of R)) := Over.homMk p₂.1 p₂.2
    have hP : P₁ ≫ (𝒰.f i).asOver (Spec (CommRingCat.of R)) = P₂ ≫ (𝒰.f j).asOver (Spec (CommRingCat.of R)) := by
      ext
      exact hp
    have h := congrArg Subtype.val (hx i j (Over.mk z) P₁ P₂ hP)
    rw [relSubPicPresheaf_map_coe, relSubPicPresheaf_map_coe] at h
    change RigidifiedLineBundle.classesMap p₁ (x i).1 = RigidifiedLineBundle.classesMap p₂ (x j).1 at h
    rw [← hM i, ← hM j] at h
    exact Quotient.exact h

  obtain ⟨N, hN⟩ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_gluing_openCover_of_bijective_sections
      R c ε hH0 Y.hom u f hf M hcompat

  have hNP : FibrewiseAlgEquivZero N :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullbackAlong_openCover
      R c ε Y.hom u f hf N (fun i =>
        (algEquivZeroCut c ε).congr _ (M i) (N.pullbackAlong (f i)) ⟨(hN i).some.symm⟩ (hMP i))

  have hmap : ∀ (i : 𝒰.I₀) (y : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op Y))
      (N' : RigidifiedLineBundle c ε Y.hom), y.1 = Quotient.mk _ N' →
      ((relSubPicPresheaf c ε (algEquivZeroCut c ε)).map
        ((𝒰.f i).asOver (Spec (CommRingCat.of R))).op y).1 = Quotient.mk _ (N'.pullbackAlong (f i)) := by
    intro i y N' hy
    rw [relSubPicPresheaf_map_coe, hy]
    rfl
  let y₀ : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op Y) :=
    ⟨Quotient.mk _ N, (SubPicCondition.onClasses_mk (algEquivZeroCut c ε) Y.hom N).2 hNP⟩
  refine ⟨y₀, ?_, ?_⟩
  ·
    intro i
    apply Subtype.ext
    rw [← hM i]
    exact (hmap i y₀ N rfl).trans (Quotient.sound (hN i))
  ·
    intro y hy
    apply Subtype.ext
    obtain ⟨N', hN'⟩ := Quotient.exists_rep y.1
    have hiso : ∀ i, Nonempty ((N'.pullbackAlong (f i)).L ≅ (N.pullbackAlong (f i)).L) := fun i => by
      have h₁ : (Quotient.mk _ (N'.pullbackAlong (f i)) : RigidifiedLineBundle.Classes c ε (u i)) =
          Quotient.mk _ (M i) :=
        (hmap i y N' hN'.symm).symm.trans ((congrArg Subtype.val (hy i)).trans (hM i).symm)
      exact ⟨(Quotient.exact h₁).some ≪≫ (hN i).some.symm⟩
    rw [← hN']
    exact Quotient.sound
      (AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
        R c ε hH0 Y.hom u f hf N' N hiso)
