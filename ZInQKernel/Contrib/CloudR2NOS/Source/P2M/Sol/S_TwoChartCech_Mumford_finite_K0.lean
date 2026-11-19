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
  Source file    : P2M/Sol/S_TwoChartCech_Mumford_finite_K0.lean
  Source sha256  : ff8e97121962492beaf30525ee4e22ae7c6d0ccc1ed8826a058d343dad1e08fa
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_TwoChartCech_Mumford_finite_K0
r2nos_namespace_dual

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

universe u v w

namespace TwoChartCech
r2nos_namespace_dual
w03_export "TwoChartCech" "Mumford.K0"
namespace Mumford
r2nos_namespace_dual
w03_export "TwoChartCech.Mumford" "rank lift K0 mem_K0_iff dK ι0 dK_apply ι0_apply"
w03_open "TwoChartCech.Mumford TwoChartCech"

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def kerToK0 : LinearMap.ker d →ₗ[R] K0 d :=
  LinearMap.codRestrict (K0 d)
    ((LinearMap.inl R C0 (Fin (rank d) → R)).comp (LinearMap.ker d).subtype)
    (fun ⟨x, hx⟩ => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.inl_apply,
        LinearMap.coprod_apply, map_zero, add_zero]
      exact hx)

def kerEquiv : LinearMap.ker (dK d) ≃ₗ[R] LinearMap.ker d := by
  refine LinearEquiv.ofLinear
    (LinearMap.codRestrict (LinearMap.ker d) ((ι0 d).comp (LinearMap.ker (dK d)).subtype) ?_)
    (LinearMap.codRestrict (LinearMap.ker (dK d)) (kerToK0 d) (fun x => by
      simp only [LinearMap.mem_ker, dK_apply]; rfl))
    ?_ ?_
  · rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hxv' : d x + lift d v = 0 := (mem_K0_iff d _).mp hxv
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, ι0_apply]
    simpa [hv', map_zero, add_zero] using hxv'
  · apply LinearMap.ext; rintro ⟨x, hx⟩; rfl
  · apply LinearMap.ext; rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    apply Subtype.ext; apply Subtype.ext
    show ((x, 0) : C0 × _) = (x, v)
    rw [hv']

end TwoChartCech.Mumford

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.TwoChartCech.Mumford _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_TwoChartCech_Mumford_finite_K0.TwoChartCech.Mumford in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.TwoChartCech.Mumford _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_TwoChartCech_Mumford_finite_K0.TwoChartCech.Mumford" in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Finite R (TwoChartCech.Mumford.K0 d) := by
  haveI hker : Module.Finite R (LinearMap.ker (dK d)) := Module.Finite.equiv (kerEquiv d).symm
  haveI hquot : Module.Finite R (K0 d ⧸ LinearMap.ker (dK d)) := by
    haveI : Module.Finite R (LinearMap.range (dK d)) := inferInstance
    exact Module.Finite.equiv (dK d).quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (dK d))

end
end S_TwoChartCech_Mumford_finite_K0
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
