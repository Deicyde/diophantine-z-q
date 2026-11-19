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
  Source file    : P2M/Sol/S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen.lean
  Source sha256  : 48594102c0e23bb7578cf116aea41cdfe89a1d6fe6757fc89e7ed91a2d1ca4ca
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve
r2nos_open_dual "CategoryTheory AlgebraicGeometry AlgebraicCurve"

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (algebraMap Γ(C, U) C.functionField).range =
      ⨅ (v : AlgebraicCurve.Place K C.functionField)
        (_ : ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
          (algebraMap (C.presheaf.stalk x) C.functionField).range =
            v.toValuationSubring.toSubring),
        v.toValuationSubring.toSubring := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  rw [hU.range_algebraMap_functionField_eq_iInf]
  apply le_antisymm
  ·
    refine le_iInf₂ fun v hv => ?_
    obtain ⟨x, hxU, -, hrange⟩ := hv
    rw [← hrange]
    exact iInf₂_le x hxU
  ·
    refine le_iInf₂ fun x hxU => ?_
    by_cases hη : x = genericPoint C
    ·
      subst hη
      intro f _
      refine ⟨f, ?_⟩
      change (C.presheaf.stalkSpecializes (specializes_refl _)).hom f = f
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    · have hxcl : IsClosed ({x} : Set C) := isClosed_singleton_of_ne_genericPoint c x hη
      obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hxcl
      rw [hv]
      exact iInf₂_le v ⟨x, hxU, hxcl, hv⟩
end S_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
