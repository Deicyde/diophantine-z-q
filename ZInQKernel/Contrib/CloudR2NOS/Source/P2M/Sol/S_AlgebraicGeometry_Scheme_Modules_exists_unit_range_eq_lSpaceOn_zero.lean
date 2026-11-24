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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero.lean
  Source sha256  : 54848f4bb88913e686bda64f2d54bcc83746503e60a76d92b78281ffeea8fc1c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 9 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 8 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 7 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
r2nos_erase_attr "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Modules.presheaf Scheme.germToFunctionField_injective Spec IsIntegral Scheme IsAffineOpen Scheme.Modules"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Modules.presheaf germToFunctionField_injective Γ empty functionField Modules Opens"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "presheaf"
namespace UnitFF
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"
open AlgebraicCurve TopologicalSpace Opposite
r2nos_open_dual "AlgebraicCurve TopologicalSpace Opposite"

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

noncomputable abbrev OU (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

omit [IsIntegral X] in

theorem smul_eq (U : X.Opens) (a : Γ(X, U)) (m : Γ(OU X, U)) :
    (show Γ(X, U) from a • m) = a * (show Γ(X, U) from m) := rfl

omit [IsIntegral X] in

theorem map_eq {U V : X.Opens} (h : V ≤ U) (m : Γ(OU X, U)) :
    (show Γ(X, V) from (OU X).presheaf.map (homOfLE h).op m) = X.presheaf.map (homOfLE h).op (show Γ(X, U) from m) :=
  rfl

noncomputable def φ (U : X.Opens) : Γ(OU X, U) →+ (X.functionField : Type u) :=
  open Classical in
  if h : Nonempty U then
    { toFun := fun m => (X.germToFunctionField U).hom (show Γ(X, U) from m)
      map_zero' := map_zero (X.germToFunctionField U).hom
      map_add' := fun m m' => map_add (X.germToFunctionField U).hom (show Γ(X, U) from m) (show Γ(X, U) from m') }
  else 0

theorem φ_apply (U : X.Opens) [h : Nonempty U] (m : Γ(OU X, U)) :
    φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m) := by
  simp only [φ, dif_pos h]
  rfl

theorem φ_nat {U V : X.Opens} (h : V ≤ U) [Nonempty U] [Nonempty V] (m : Γ(OU X, U)) :
    φ V ((OU X).presheaf.map (homOfLE h).op m) = φ U m := by
  rw [φ_apply, φ_apply, map_eq]
  show (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField V).hom _ = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]

theorem φ_smul (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(OU X, U)) :
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m := by
  rw [φ_apply, φ_apply, smul_eq, map_mul]
  rfl

theorem φ_injective (U : X.Opens) [Nonempty U] : Function.Injective (φ (X := X) U) := by
  intro m m' h
  rw [φ_apply, φ_apply] at h
  exact Scheme.germToFunctionField_injective X U h

theorem range_φ [SmoothOfRelativeDimension 1 x] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (baseToFunctionField x).toAlgebra
    Set.range (φ (X := X) U) = (lSpaceOn (placesOf x U) (0 : Divisor K X.functionField) : Set X.functionField) := by
  letI := (baseToFunctionField x).toAlgebra
  have hsec := range_algebraMap_functionField_eq_iInf_of_isAffineOpen x U hU
  ext f
  have h1 : f ∈ Set.range (φ (X := X) U) ↔ f ∈ (algebraMap Γ(X, U) X.functionField).range := by
    simp only [Set.mem_range, RingHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨show Γ(X, U) from m, by rw [φ_apply]; rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨show Γ(OU X, U) from a, by rw [φ_apply]; rfl⟩
  rw [h1, hsec, SetLike.mem_coe, mem_lSpaceOn_iff]
  simp only [Subring.mem_iInf, Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  constructor
  · intro hf v hv
    exact (Place.mem_iff_adicValuation_le_one v).mp (hf v hv)
  · intro hf v hv
    exact (Place.mem_iff_adicValuation_le_one v).mpr (hf v hv)

end AlgebraicGeometry.Scheme.Modules.UnitFF

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.germToFunctionField SmoothOfRelativeDimension Scheme.Modules.presheaf Scheme.germToFunctionField_injective Spec IsIntegral Scheme IsAffineOpen Scheme.Modules"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "germToFunctionField ringCatSheaf Modules.presheaf germToFunctionField_injective Γ empty functionField Modules Opens"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "presheaf"
end AlgebraicGeometry.Scheme.Modules
r2nos_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
open AlgebraicGeometry.Scheme.Modules.UnitFF in
r2nos_open_dual "AlgebraicGeometry.Scheme.Modules.UnitFF" in

theorem AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero'
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+ (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  refine ⟨fun U => φ U, fun U _ m => φ_apply U m, ?_, fun U _ a m => φ_smul U a m,
    fun U hU => by haveI := hU; exact φ_injective U, fun U hU hne => by haveI := hne; exact range_φ x U hU⟩
  intro U V h hV m
  haveI := hV
  haveI : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
  exact φ_nat h m

open AlgebraicGeometry.Scheme.Modules.UnitFF in
r2nos_open_dual "AlgebraicGeometry.Scheme.Modules.UnitFF" in
theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+ (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) :=
  AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero' x
end S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
