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
  Source file    : P2M/Sol/S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve.lean
  Source sha256  : ca032a7b9fb9916f3bf37bb4e35d28965405e3cef9b93df069929d8bb33315ad
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
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 15 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
r2nos_erase_attr "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

universe u

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Divisor H1 genusFF IsCurveOver LSpace ell RiemannGenusReachedAt baseToFunctionField nonempty_linearEquiv_cechH0_and_cechH1 placesOf_union_eq_univ_of_sup_eq_top cechRiemannRoch_of_genusReached indexOfSpecialty_eq_finrank_H1"
w03_open "AlgebraicCurve"
open CategoryTheory AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory AlgebraicGeometry TopologicalSpace"

theorem nonempty_of_sup_eq_top {C : Scheme.{u}} (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hV : V ≠ ⊤) :
    Nonempty U := by
  have hUne : (U : Set C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact hV hUV
  exact hUne.to_subtype

theorem ne_top_of_isAffineOpen {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

theorem finite_H0_H1_structureSheaf_of_smoothProperCurve' {K : Type u} [Field K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hcurve : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      AlgebraicCurve.IsCurveOver K C.functionField)
    (hL0 : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K C.functionField)))
    (hreach : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      ∃ (γ : ℤ) (D₀ : AlgebraicCurve.Divisor K C.functionField), AlgebraicCurve.RiemannGenusReachedAt γ D₀) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0
        = AlgebraicCurve.ell (0 : AlgebraicCurve.Divisor K C.functionField) ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI := hcurve
  haveI := hL0
  obtain ⟨γ, D₀, hγ⟩ := hreach
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen hNA 𝒱.isAffineOpen_U1
  have h0 : Nonempty 𝒱.U0 := nonempty_of_sup_eq_top 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne1
  have h1 : Nonempty 𝒱.U1 := nonempty_of_sup_eq_top 𝒱.U1 𝒱.U0 (sup_comm 𝒱.U1 𝒱.U0 ▸ 𝒱.sup_eq_top) hne0
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_cechH0_and_cechH1 𝒱 c h0 h1
  obtain ⟨hcov, hS0, hS1⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1
  obtain ⟨hfin0, hfin1, hrk0, hrk1, -, -⟩ :=
    cechRiemannRoch_of_genusReached hγ hcov hS0 hS1 (0 : Divisor K C.functionField)
  refine ⟨Module.Finite.equiv e0.symm, Module.Finite.equiv e1.symm, ?_, ?_⟩
  · rw [e0.finrank_eq, hrk0]
  · rw [e1.finrank_eq, hrk1, indexOfSpecialty_eq_finrank_H1]
    rfl

end AlgebraicCurve

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve.AlgebraicCurve in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve.AlgebraicCurve" in
theorem solution {K : Type u} [Field K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hcurve : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      AlgebraicCurve.IsCurveOver K C.functionField)
    (hL0 : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K C.functionField)))
    (hreach : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      ∃ (γ : ℤ) (D₀ : AlgebraicCurve.Divisor K C.functionField), AlgebraicCurve.RiemannGenusReachedAt γ D₀) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0
        = AlgebraicCurve.ell (0 : AlgebraicCurve.Divisor K C.functionField) ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField :=
  finite_H0_H1_structureSheaf_of_smoothProperCurve' 𝒱 c hcurve hL0 hreach
end S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
