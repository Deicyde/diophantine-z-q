/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_CategoryTheory_OverTotalPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicGlue
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AffineLimit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_AffineLimit_homIsLFP_of_locallyOfFinitePresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_HasChartSections_forall_geometricFibre_riemannRoch_imp_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_finiteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve hiding genus
open AlgebraicGeometry.AffineLimit

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (n g r : ℕ) (hgr : 2 * g < r)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hγ : HasChartSections c γ) :
    ∃ (X : ULift.{u} (Fin n) → Scheme.{u})
      (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      (∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i)) ∧
        Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) := by

  have hg := AlgebraicGeometry.RelPicard.HasChartSections.forall_geometricFibre_riemannRoch_imp_eq hγ

  have hD : ∀ i : Fin n, ∃ D : RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))),
      D.I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2) := fun i =>
    AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph (fun j => (γ i j).1) (fun j => (γ i j).2)
  choose Dγ hDγ using hD
  have hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1 :=
    fun i k _ _ x 𝒲 =>
      AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
        R c ε g (r - g) r (by omega) (Dγ i) hg k x 𝒲

  have hch := fun i : ULift.{u} (Fin n) =>
    AlgebraicGeometry.RelPicard.exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
      R c ε h𝔉 g (r - g) r (by omega) (Dγ i.down) (hχ i.down)
  choose X f hlft hchart using hch
  refine ⟨X, f, ?_⟩
  have hG : Presieve.IsSheaf Scheme.zariskiTopology (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal :=
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal_isSheaf _
      (AlgebraicGeometry.RelPicard.isSheaf_relSubPicPresheaf_algEquivZeroCut_zariski_of_finiteMapData R c ε h𝔉)
  refine AlgebraicGeometry.AffineLimit.presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
    R _ hG
    (AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut R c ε h𝔉)
    (AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_algEquivZeroCut R c ε h𝔉)
    X f (fun i => by haveI := hlft i; exact AlgebraicGeometry.AffineLimit.homIsLFP_of_locallyOfFinitePresentation R _) ?_
  intro T x hx
  have hc := fun i => hchart i x hx
  choose U φ hU using hc
  refine ⟨U, φ, ?_, fun i => ⟨(hU i).2.1, (hU i).2.2⟩⟩

  rw [eq_top_iff]
  rintro p -
  let t := (uliftYonedaEquiv x).1
  haveI : LocallyOfFiniteType t := hx
  let L : RigidifiedLineBundle c ε t := Quotient.out (uliftYonedaEquiv x).2.1
  have hLx : Quotient.mk _ L = (uliftYonedaEquiv x).2.1 := Quotient.out_eq _
  have hL : FibrewiseAlgEquivZero L := by
    have h2 := (uliftYonedaEquiv x).2.2
    rw [← hLx] at h2
    exact h2
  obtain ⟨i, hi⟩ := AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre R c ε n g r hgr hg γ hγ Dγ hDγ hχ t L hL
    (T.residueField p) (T.fromSpecResidueField p)
  have hmem : Set.range ⇑(T.fromSpecResidueField p) ⊆ (U ⟨i⟩ : Set T) :=
    ((hU ⟨i⟩).1 L hLx (T.residueField p) (T.fromSpecResidueField p)).mpr hi
  have hp : p ∈ U ⟨i⟩ := hmem ⟨IsLocalRing.closedPoint _, by simp⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hp⟩
