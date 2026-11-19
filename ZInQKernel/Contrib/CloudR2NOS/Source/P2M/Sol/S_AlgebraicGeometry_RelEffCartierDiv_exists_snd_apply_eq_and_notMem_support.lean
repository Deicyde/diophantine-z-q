/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support.lean
  Source sha256  : fb7893eff83c7a5a2aa3659b18fadaa08e2b1b3ca9a4ffcb6844513b93edefb6
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 12 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
r2nos_erase_attr "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Hom.finite_preimage_singleton SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.Hom.range_fiberι GeometricallyIrreducible IsFinite Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Smooth IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.IdealSheafData isIntegral_of_irreducibleSpace_of_isReduced RelEffCartierDiv isReduced_of_smooth_over_field"
namespace RelEffCartierDiv
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelEffCartierDiv" "I isFinite"
namespace OffSupportSol
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

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
end S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
