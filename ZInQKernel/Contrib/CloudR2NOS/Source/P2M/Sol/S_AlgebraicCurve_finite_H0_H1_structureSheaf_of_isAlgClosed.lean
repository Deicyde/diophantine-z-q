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
  Source file    : P2M/Sol/S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed.lean
  Source sha256  : b986627756cfdf2c243e936977b1e48acfb3f6e6831a17781f76481210124cf6
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 4 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 17 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
r2nos_erase_attr "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
r2nos_erase_attr "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
r2nos_erase_attr "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

universe u

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "H1 genusFF IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed ConstantsAreBase ell_zero_eq_one_of_constantsAreBase baseToFunctionField finite_H0_H1_structureSheaf_of_smoothProperCurve placesOf_union_eq_univ_of_sup_eq_top isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one essFiniteType_functionField constantsAreBase_of_deg_eq_one stichtenothGenusExists_of_isCurveOver"
w03_open "AlgebraicCurve"
open CategoryTheory AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory AlgebraicGeometry TopologicalSpace"

theorem ne_top_of_isAffineOpen' {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

theorem finite_H0_H1_structureSheaf_of_isAlgClosed' {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0 = 1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  haveI hcurve : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K C.functionField := essFiniteType_functionField c

  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen' hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen' hNA 𝒱.isAffineOpen_U1
  obtain ⟨-, ⟨v₀, -⟩, -⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1

  have hC : ConstantsAreBase K C.functionField :=
    constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  obtain ⟨-, hL0, γ, D₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
  obtain ⟨hf0, hf1, hrk0, hrk1⟩ :=
    finite_H0_H1_structureSheaf_of_smoothProperCurve 𝒱 c hcurve hL0 ⟨γ, D₀, hγ⟩
  exact ⟨hf0, hf1, hrk0.trans (ell_zero_eq_one_of_constantsAreBase hC), hrk1⟩

end AlgebraicCurve

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed.AlgebraicCurve in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed.AlgebraicCurve" in
theorem solution {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0 = 1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField :=
  finite_H0_H1_structureSheaf_of_isAlgClosed' 𝒱 c
end S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
