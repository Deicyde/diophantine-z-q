/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open CategoryTheory.MonoidalCategory
open GoodReductionJacobian
open AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 =
          r + 1 - g := by
  intro k _ _ s 𝒲

  let σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := s ≫ t
  let ψ : SchemeHomOver σ t := ⟨s, rfl⟩
  let κ : pullback (pullback.snd c t) s ≅ pullback c σ := pullbackLeftPullbackSndIso c t s
  have hκsnd : κ.inv ≫ fibreAt c t s = pullback.snd c σ := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd c t s).symm
  have hκbcs : κ.inv ≫ pullback.fst (pullback.snd c t) s = baseChangeSnd c ψ := by
    rw [Iso.inv_comp_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeSnd, pullback.lift_fst, Category.comp_id]
      exact (pullbackLeftPullbackSndIso_hom_fst c t s).symm
    · rw [Category.assoc, baseChangeSnd, pullback.lift_snd, pullback.condition, ← Category.assoc,
        pullbackLeftPullbackSndIso_hom_snd]

  obtain ⟨iTw⟩ := RelPicard.nonempty_pullback_sectionTwist_iso R c ε ψ r
  let e : (M.pullbackAlong ψ).L ⊗ (((rigSection c σ ε).ker) ^ r).invModule ≅
      (Scheme.Modules.pullback κ.symm.hom).obj
        (fibreModule c t s (M.L ⊗ sectionTwist c ε t r)) :=
    ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hκbcs).app _ ≪≫
      Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) M.L (sectionTwist c ε t r) ≪≫
      whiskerLeftIso _ iTw).symm
  obtain ⟨𝒱, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (pullback.snd c σ) (fibreAt c t s)
      κ.symm hκsnd 𝒲 _ _ e

  have h0 : IsAlgEquivZero (pullback.snd c σ) (M.pullbackAlong ψ).L :=
    IsAlgEquivZero.of_iso ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hκbcs).app _)
      ((hM k s).pullback κ.inv hκsnd)

  obtain ⟨h1, h0'⟩ :=
    AlgebraicGeometry.subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
      k (pullback.snd c σ) g (fun L _ _ M e' he Kc g' hRR => hg k σ L M e' he Kc g' hRR)
      (rigSection c σ ε) (pullback.lift_snd _ _ _) (M.pullbackAlong ψ).L
      (M.pullbackAlong ψ).isInvertible h0 r hr 𝒱
  refine ⟨?_, ?_⟩
  · haveI := h1
    exact eH1.symm.toEquiv.subsingleton
  · rw [← eH0.finrank_eq]
    exact h0'
