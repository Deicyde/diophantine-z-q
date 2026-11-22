/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker. Apache-2.0.
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
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open CategoryTheory.MonoidalCategory
open AlgebraicCurve

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (m : ℕ) (hm : 2 * g ≤ m + 1) (𝒱 : C.TwoAffineOpenCover)
    (K : Type u) [Field K] [Algebra R K] :
    Subsingleton ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj
          ((ε.1.ker ^ m).invModule))).H1 ∧
      Module.finrank K ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj
          ((ε.1.ker ^ m).invModule))).H0 = m + 1 - g := by

  let S : Scheme.{u} := Spec (CommRingCat.of R)
  let sK : Spec (CommRingCat.of K) ⟶ S := Scheme.TwoAffineOpenCover.specMap R K
  let ψ : SchemeHomOver sK (𝟙 S) := ⟨sK, Category.comp_id _⟩
  let g' : pullback c sK ⟶ pullback c (𝟙 S) := baseChangeSnd c ψ
  let π : pullback c (𝟙 S) ⟶ C := pullback.fst c (𝟙 S)
  have hg'π : g' ≫ π = pullback.fst c sK := by
    simp only [g', π, baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hg'snd : g' ≫ pullback.snd c (𝟙 S) = pullback.snd c sK ≫ sK := by
    simp only [g', baseChangeSnd, pullback.lift_snd]
    rfl

  have hcart : IsPullback g' (pullback.snd c sK) (pullback.snd c (𝟙 S)) sK := by
    refine IsPullback.of_right ?_ hg'snd (IsPullback.of_hasPullback c (𝟙 S))
    rw [hg'π, Category.comp_id]
    exact IsPullback.of_hasPullback c sK

  have hεc : ε.1 ≫ c = 𝟙 S := ε.2
  haveI : IsClosedImmersion (ε.1 ≫ c) := by rw [hεc]; infer_instance
  haveI : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hI : ε.1.ker.IsCartierFLT := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 hεc
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (𝟙 S)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσ : rigSection c (𝟙 S) ε ≫ pullback.snd c (𝟙 S) = 𝟙 S := by
    simp only [rigSection, pullback.lift_snd]
  have hI' : (rigSection c (𝟙 S) ε).ker.IsCartierFLT :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (𝟙 S) ε) hσ
  have hσπ : rigSection c (𝟙 S) ε ≫ π = ε.1 := by
    simp only [rigSection, π, pullback.lift_fst, Category.id_comp]

  obtain ⟨eπ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso π ε.1
    (rigSection c (𝟙 S) ε) hσπ hI hI' m).1

  let N : C.Modules := (ε.1.ker ^ m).invModule
  let M : (pullback c (𝟙 S)).Modules :=
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 S)).L ⊗ sectionTwist c ε (𝟙 S) m
  have eS : (Scheme.Modules.pullback π).obj N ≅ M :=
    eπ ≪≫ (λ_ (sectionTwist c ε (𝟙 S) m)).symm
  have e : (Scheme.Modules.pullback (pullback.fst c sK)).obj N ≅ (Scheme.Modules.pullback g').obj M :=
    (Scheme.Modules.pullbackCongr hg'π.symm).app N ≪≫ ((Scheme.Modules.pullbackComp g' π).app N).symm ≪≫
      (Scheme.Modules.pullback g').mapIso eS

  obtain ⟨𝒲, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c (𝟙 S) M sK
      (pullback.snd c sK) g' hcart ((Scheme.Modules.pullback (pullback.fst c sK)).obj N) e (𝒱.pullback c K)

  obtain ⟨h1, h0⟩ :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
      R c ε g hg (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 S)) (fibrewiseAlgEquivZero_unit (𝟙 S)) m hm K sK 𝒲
  haveI := h1
  exact ⟨eH1.toEquiv.subsingleton, eH0.finrank_eq.trans h0⟩
