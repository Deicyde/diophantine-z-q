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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel.lean
  Source sha256  : 3da2df7f70b57ea6ee8a317b5d56d1b3e7b76d630169fdd59c35fd5e09140bb4
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel
r2nos_namespace_dual

set_option autoImplicit false

universe u

namespace Ideal
r2nos_namespace_dual
w03_export "Ideal" "span mem_span_singleton_mul"
end Ideal
r2nos_open_scoped "Ideal" in

theorem Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {a : R} (ha : a ∈ nonZeroDivisors R) :
    Function.Injective fun K : Ideal R ↦ Ideal.span {a} * K := by

  suffices key : ∀ K K' : Ideal R, Ideal.span {a} * K = Ideal.span {a} * K' → K ≤ K' from
    fun K K' h ↦ le_antisymm (key K K' h) (key K' K h.symm)
  intro K K' h x hx
  have hax : a * x ∈ Ideal.span {a} * K' := h ▸ Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := Ideal.mem_span_singleton_mul.mp hax
  rwa [← (mul_cancel_left_mem_nonZeroDivisors ha).mp hyx]

open AlgebraicGeometry
r2nos_open_dual "AlgebraicGeometry"

theorem solution {X : Scheme.{u}}
    {I J J' : X.IdealSheafData} (hI : I.IsInvertible) (h : I * J = I * J') : J = J' := by
  choose U f hxf g hg hIg using hI
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun x : X ↦ X.affineBasicOpen (f x)) ?_ ?_
  · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxf x⟩
  · intro x
    have hx := congrArg (fun K : X.IdealSheafData ↦ K.ideal (X.affineBasicOpen (f x))) h
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hIg] at hx
    exact Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors (hg x) hx
end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
