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
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso.lean
  Source sha256  : 73084c7457f789fd39e2f966947a058e27d355d64c3e6c469d449af04d4aa216
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 7 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

r2nos_erase_attr "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)
    (ι : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hι : ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (J0 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A0)
    (J1 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A1)
    (J01 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A01) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
    let σst := RelPicard.baseChangeSnd c
      (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))
    let A0B := (𝒱B.cover cB).A0
    let A1B := (𝒱B.cover cB).A1
    let A01B := (𝒱B.cover cB).A01
    let P0 := (𝒱BI.sectionsOf cBI M).M0
    let P1 := (𝒱BI.sectionsOf cBI M).M1
    ∀ (φ0 : A0B ⧸ J0 ≃+* (𝒱BI.cover cBI).A0)
      (φ1 : A1B ⧸ J1 ≃+* (𝒱BI.cover cBI).A1)
      (φ01 : A01B ⧸ J01 ≃+* (𝒱BI.cover cBI).A01)
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ0 a)) =
                (𝒱BI.cover cBI).ρ0 (φ0 (Ideal.Quotient.mk J0 a)))
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ1 a)) =
                (𝒱BI.cover cBI).ρ1 (φ1 (Ideal.Quotient.mk J1 a)))
      (_ : ∀ a, φ0 (Ideal.Quotient.mk J0 a) =
          (σst.appLE 𝒱B.U0 𝒱BI.U0
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a)
      (_ : ∀ a, φ1 (Ideal.Quotient.mk J1 a) =
          (σst.appLE 𝒱B.U1 𝒱BI.U1
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a)
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 a) =
          (σst.appLE (𝒱B.U0 ⊓ 𝒱B.U1) (𝒱BI.U0 ⊓ 𝒱BI.U1)
            (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R B (B ⧸ I)))).ge).hom a)
      (P0' : Type u) [AddCommGroup P0'] [Module A0B P0']
      (P1' : Type u) [AddCommGroup P1'] [Module A1B P1'],
      letI : Module (A0B ⧸ J0) P0 := Module.compHom P0 φ0.toRingHom
      letI : Module (A1B ⧸ J1) P1 := Module.compHom P1 φ1.toRingHom
      ∀ (iso0 : (A0B ⧸ J0) ⊗[A0B] P0' ≃ₗ[A0B ⧸ J0] P0)
        (iso1 : (A1B ⧸ J1) ⊗[A1B] P1' ≃ₗ[A1B ⧸ J1] P1),
      letI : Algebra A0B A01B := (𝒱B.cover cB).ρ0.toRingHom.toAlgebra
      letI : Algebra A1B A01B := (𝒱B.cover cB).ρ1.toRingHom.toAlgebra
      letI : Module (A01B ⧸ J01) (𝒱BI.sectionsOf cBI M).M01 := Module.compHom _ φ01.toRingHom
      ∀ (σ' : A01B ⊗[A0B] P0' ≃ₗ[A01B] A01B ⊗[A1B] P1')
        (iso01 : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A0B] P0') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01)
        (_ : ∀ (p : P0'), iso01 ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A0B] p)) =
              (𝒱BI.sectionsOf cBI M).r0 (iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p)))
        (_ : ∀ (p : P1'), iso01 ((1 : A01B ⧸ J01) ⊗ₜ[A01B] (σ'.symm ((1 : A01B) ⊗ₜ[A1B] p))) =
              (𝒱BI.sectionsOf cBI M).r1 (iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p)))
        (L' : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R B)).Modules)
        (_ : Scheme.Modules.IsInvertible L')
        (e0' : (𝒱B.sectionsOf cB L').M0 ≃ₗ[A0B] P0')
        (e1' : (𝒱B.sectionsOf cB L').M1 ≃ₗ[A1B] P1')
        (e01' : (𝒱B.sectionsOf cB L').M01 ≃ₗ[A01B] A01B ⊗[A0B] P0')
        (_ : ∀ m, e01' ((𝒱B.sectionsOf cB L').r0 m) = (1 : A01B) ⊗ₜ[A0B] e0' m)
        (_ : ∀ m, σ' (e01' ((𝒱B.sectionsOf cB L').r1 m)) = (1 : A01B) ⊗ₜ[A1B] e1' m),
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ι)).obj L' ≅ M) := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
