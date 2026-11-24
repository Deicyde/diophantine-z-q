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
  Source file    : P2M/Sol/S_RingTheory_Sequence_isWeaklyRegular_of_free_aux.lean
  Source sha256  : 6f770d258105c3b0dd9d9cbc4c7e22dbaebb65914561d42a3f56040caf8760e8
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_isSMulRegular_iff_of_free
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free_aux
r2nos_namespace_dual

open scoped Pointwise TensorProduct
r2nos_open_scoped_dual "Pointwise TensorProduct"

theorem solution.{u, v} {R : Type u} {M : Type max u v} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by
  generalize hn : s.length = n
  induction n generalizing R M with
  | zero => simp_all
  | succ n IH =>
    cases s with
    | nil => simp at hn
    | cons x xs =>
    let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} := Submodule.quotEquivOfEq _ _
      (by rw [← Submodule.ideal_span_singleton_smul]; simp)
    let e' := QuotSMulTop.equivQuotTensor x M
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff,
      e.isWeaklyRegular_congr, e'.isWeaklyRegular_congr,
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x}),
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R := R) (R ⧸ Ideal.span {x})]
    refine and_congr isSMulRegular_iff_of_free ?_
    cases subsingleton_or_nontrivial (R ⧸ Ideal.span {x})
    · haveI : Subsingleton ((R ⧸ Ideal.span {x}) ⊗[R] M) := Module.subsingleton (R ⧸ Ideal.span {x}) _
      exact iff_of_true
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
    exact IH (by simp_all)
end S_RingTheory_Sequence_isWeaklyRegular_of_free_aux
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
