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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.lean
  Source sha256  : 90d1044dc3c34e5940f860074ef826c9b8873fc1010d86de91c506dd2da4c99c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`; `set_option maxHeartbeats 6400000 in`; `set_option synthInstance.maxHeartbeats 1600000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 8 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
r2nos_namespace_dual
r2nos_erase_attr "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
r2nos_erase_attr "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.IdealSheafData.one_eq_top Scheme.IdealSheafData.le_map_comap Scheme.Modules.pullback Scheme.Hom Scheme.IdealSheafData.map_ker Scheme.IdealSheafData.map_id Scheme Scheme.IdealSheafData.comap_top IsClosedImmersion Scheme.IdealSheafData.map_comp Scheme.IdealSheafData.map_mono Scheme.Modules Scheme.IdealSheafData.comap_map_le Scheme.IdealSheafData Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison"
namespace BCKerGlue
r2nos_namespace_dual
w03_open "AlgebraicGeometry"


theorem comap_eq_map_inv {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (J : X.IdealSheafData) :
    J.comap f = J.map (inv f) := by
  apply le_antisymm
  · have h : ((J.map (inv f)).map f).comap f ≤ J.map (inv f) :=
      Scheme.IdealSheafData.comap_map_le (J.map (inv f)) f
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.map_id] at h
  · have h : J.map (inv f) ≤ ((J.comap f).map f).map (inv f) :=
      Scheme.IdealSheafData.map_mono (inv f) (Scheme.IdealSheafData.le_map_comap J f)
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.map_id] at h


theorem ker_comap_eq_ker {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) (p' : T ⟶ Y)
    (hp : p' ≫ f = p) : p.ker.comap f = p'.ker := by
  rw [comap_eq_map_inv, Scheme.IdealSheafData.map_ker, ← hp, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]


theorem comap_pow {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | succ n ih =>
      rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

end AlgebraicGeometry.BCKerGlue

open AlgebraicGeometry.BCKerGlue in
r2nos_open_dual "AlgebraicGeometry.BCKerGlue" in
theorem solution
    {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) [IsClosedImmersion p] (p' : T ⟶ Y)
    (hp : p' ≫ f = p) (hI : p.ker.IsInvertible) (hI' : p'.ker.IsInvertible) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).invModule) ≅ ((p'.ker) ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).module) ≅ ((p'.ker) ^ n).module) := by

  have hk : (p.ker ^ n).comap f = p'.ker ^ n := by
    rw [comap_pow, ker_comap_eq_ker f p p' hp]
  have hIn : (p.ker ^ n).IsInvertible := hI.pow n
  have hIn' : ((p.ker ^ n).comap f).IsInvertible := by
    rw [hk]
    exact hI'.pow n
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f hIn hIn'
    exact ⟨e ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hk)⟩
  · have h := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hIn hIn'
    exact ⟨@asIso _ _ _ _ ((p.ker ^ n).pullbackModuleComparison f) h ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hk)⟩
end S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
