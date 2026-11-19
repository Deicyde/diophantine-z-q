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
  Source file    : P2M/Sol/S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm.lean
  Source sha256  : c130e4d4cfcc8fcd76f21d2c465ae2df9d0479b2c20e1e2cf04a3b6364819990
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
r2nos_namespace_dual

set_option autoImplicit false

universe u v w

namespace LinearMap
r2nos_namespace_dual
w03_export "LinearMap" "mem_range range coe_coe ext submoduleMap ker mem_ker"
w03_open "LinearMap"

section KerModRange

variable {R : Type u} [CommRing R] {C : ℕ → Type v} {C' : ℕ → Type w}
  [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
  (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x))

include he

theorem kerModRange_map_ker (i : ℕ) :
    (LinearMap.ker (d i)).map (e i : C i →ₗ[R] C' i) = LinearMap.ker (d' i) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he, hx, map_zero]
  · intro hy
    refine ⟨(e i).symm y, ?_, by simp⟩
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hy, map_zero]

def kerEquivOfComm (i : ℕ) : LinearMap.ker (d i) ≃ₗ[R] LinearMap.ker (d' i) :=
  ((e i).submoduleMap (LinearMap.ker (d i))).trans (LinearEquiv.ofEq _ _ (kerModRange_map_ker d d' e he i))

theorem kerEquivOfComm_apply (i : ℕ) (x : LinearMap.ker (d i)) :
    ((kerEquivOfComm d d' e he i x : LinearMap.ker (d' i)) : C' i) = e i x := rfl

theorem kerModRange_map_comap (i : ℕ) :
    ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype).map
        (kerEquivOfComm d d' e he (i + 1) : LinearMap.ker (d (i + 1)) →ₗ[R] LinearMap.ker (d' (i + 1)))
      = (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨w, hw⟩, rfl⟩
    refine ⟨e i w, ?_⟩
    rw [kerEquivOfComm_apply, ← he, hw]
  · rintro ⟨w, hw⟩
    refine ⟨(kerEquivOfComm d d' e he (i + 1)).symm y, ⟨(e i).symm w, ?_⟩, by simp⟩
    have h1 : ((kerEquivOfComm d d' e he (i + 1)).symm y : C (i + 1))
        = (e (i + 1)).symm (y : C' (i + 1)) := by
      apply (e (i + 1)).injective
      rw [LinearEquiv.apply_symm_apply, ← kerEquivOfComm_apply d d' e he, LinearEquiv.apply_symm_apply]
    rw [h1]
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hw]

theorem nonempty_kerModRange_equiv_of_equiv_comm' :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) :=
  ⟨⟨kerEquivOfComm d d' e he 0⟩, fun i =>
    ⟨Submodule.Quotient.equiv _ _ (kerEquivOfComm d d' e he (i + 1)) (kerModRange_map_comap d d' e he i)⟩⟩

end KerModRange

end LinearMap

theorem solution
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) :=
  LinearMap.nonempty_kerModRange_equiv_of_equiv_comm' d d' e he
end S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
