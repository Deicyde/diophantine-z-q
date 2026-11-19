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
  Source file    : P2M/Sol/S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top.lean
  Source sha256  : 34fd73b8acbe65ae152037f45b679b84add94ca7ca181a95f6172d0e1a9add03
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
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 8 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

universe u

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place baseToFunctionField placesOf placesOf_sup exists_closedPoint_range_stalk_eq isClosed_singleton_of_ne_genericPoint exists_place_range_stalk_eq eq_of_range_stalk_eq"
w03_open "AlgebraicCurve"
open CategoryTheory AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory AlgebraicGeometry TopologicalSpace"

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]

theorem placesOf_top [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊤ : C.Opens) = Set.univ := by
  letI := (baseToFunctionField c).toAlgebra
  refine Set.eq_univ_of_forall fun v => ?_
  obtain ⟨x, hx, hv⟩ := exists_closedPoint_range_stalk_eq c v
  exact ⟨x, trivial, hx, hv⟩

theorem exists_not_mem_placesOf [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ v : Place K C.functionField, v ∉ placesOf c U := by
  letI := (baseToFunctionField c).toAlgebra

  have hUne : (U : Set C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact hV hUV
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)

  obtain ⟨x, hxU⟩ : ∃ x : C, x ∉ U :=
    not_forall.mp fun h => hU (Opens.ext (Set.eq_univ_of_forall h))
  have hxη : x ≠ genericPoint C := fun h => hxU (h ▸ hη)
  have hxcl := isClosed_singleton_of_ne_genericPoint c x hxη
  obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hxcl
  refine ⟨v, ?_⟩
  rintro ⟨y, hyU, -, hvy⟩
  have hxy : x = y := eq_of_range_stalk_eq c x y (hv.trans hvy.symm)
  exact hxU (hxy ▸ hyU)

theorem placesOf_union_eq_univ_of_sup_eq_top' [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ∪ placesOf c V = Set.univ ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c U) ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c V) := by
  letI := (baseToFunctionField c).toAlgebra
  refine ⟨?_, exists_not_mem_placesOf c U V hUV hU hV,
    exists_not_mem_placesOf c V U (sup_comm U V ▸ hUV) hV hU⟩
  rw [← placesOf_sup, hUV, placesOf_top]

end AlgebraicCurve

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top.AlgebraicCurve in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top.AlgebraicCurve" in
theorem solution {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    AlgebraicCurve.placesOf c U ∪ AlgebraicCurve.placesOf c V = Set.univ ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c U) ∧
      (∃ v : AlgebraicCurve.Place K C.functionField, v ∉ AlgebraicCurve.placesOf c V) :=
  placesOf_union_eq_univ_of_sup_eq_top' c U V hUV hU hV
end S_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
