/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Hom.finite_preimage_singleton SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.Hom.range_fiberι GeometricallyIrreducible IsFinite Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Smooth IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.IdealSheafData isIntegral_of_irreducibleSpace_of_isReduced RelEffCartierDiv isReduced_of_smooth_over_field)
namespace RelEffCartierDiv
export _root_.AlgebraicGeometry.RelEffCartierDiv (I isFinite)
namespace OffSupportSol
open AlgebraicGeometry.RelEffCartierDiv
open AlgebraicGeometry

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x : T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support := by
  classical
  let q := pullback.snd c t

  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hsm1 : SmoothOfRelativeDimension 1 q := MorphismProperty.pullback_snd c t inferInstance
  have hsm2 : SmoothOfRelativeDimension 1 (q.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd q (T.fromSpecResidueField x) hsm1
  have hsmooth : Smooth (q.fiberToSpecResidueField x) := @SmoothOfRelativeDimension.smooth 1 _ _ _ hsm2
  haveI : IsReduced (q.fiber x) := isReduced_of_smooth_over_field hsmooth
  haveI : IrreducibleSpace ↥(q.fiber x) := inferInstance
  haveI : IsIntegral (q.fiber x) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hinf : Infinite ↥(q.fiber x) := by
    have h := @AlgebraicCurve.infinite_setOf_isClosed_singleton _ _ _ (q.fiberToSpecResidueField x) inferInstance hsm2
    haveI := h.to_subtype
    exact Infinite.of_injective (fun z : {y : ↥(q.fiber x) | IsClosed ({y} : Set ↥(q.fiber x))} => (z : ↥(q.fiber x)))
      Subtype.val_injective

  haveI : IsFinite (D.I.subschemeι ≫ q) := D.isFinite
  have hfin : ((D.I.subschemeι ≫ q).base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton _ x

  by_contra hcon
  push_neg at hcon
  have hsub : ∀ z : ↥(q.fiber x), ∃ w : ↥(D.I.subscheme), D.I.subschemeι.base w = (q.fiberι x).base z := by
    intro z
    have hx : q.base ((q.fiberι x).base z) = x := by
      have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
      exact this
    have hmem := hcon _ hx
    have : (q.fiberι x).base z ∈ Set.range D.I.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hmem
    exact this
  choose w hw using hsub
  have hwS : ∀ z, w z ∈ (D.I.subschemeι ≫ q).base ⁻¹' {x} := by
    intro z
    show q.base (D.I.subschemeι.base (w z)) ∈ ({x} : Set T)
    rw [hw z]
    have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
    exact this
  haveI : Finite ↥((D.I.subschemeι ≫ q).base ⁻¹' {x}) := hfin.to_subtype
  have hinj : Function.Injective (fun z : ↥(q.fiber x) => (⟨w z, hwS z⟩ : ↥((D.I.subschemeι ≫ q).base ⁻¹' {x}))) := by
    intro z₁ z₂ h12
    have h' : w z₁ = w z₂ := congrArg Subtype.val h12
    have := (hw z₁).symm.trans ((congrArg (fun v => D.I.subschemeι.base v) h') ▸ (hw z₂))
    exact (q.fiberι x).isEmbedding.injective (by rw [← hw z₁, ← hw z₂, h'])
  haveI := Finite.of_injective _ hinj
  exact not_finite ↥(q.fiber x)

end AlgebraicGeometry.RelEffCartierDiv.OffSupportSol

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x : T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support :=
  AlgebraicGeometry.RelEffCartierDiv.OffSupportSol.main c t D x
