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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le.lean
  Source sha256  : 017c22dc7b1f082b029814c68e6be06673ff9837059a6b5f74f2d605fa15995a
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

namespace P2mVan
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem isEmpty_idx {i : ℕ} (h : Fintype.card K.ι ≤ i) : IsEmpty (K.Idx i) := by
  refine ⟨fun s => ?_⟩
  have := Fintype.card_le_of_injective s.1 s.2.injective
  rw [Fintype.card_fin] at this
  omega

theorem subsingleton_cochain {i : ℕ} (h : Fintype.card K.ι ≤ i) : Subsingleton (F.cochain K i) := by
  haveI := isEmpty_idx K h
  infer_instance

theorem subsingleton_H0 (h : Fintype.card K.ι = 0) : Subsingleton (F.H0 K) := by
  haveI := subsingleton_cochain F K h.le
  infer_instance

theorem subsingleton_HSucc {i : ℕ} (h : Fintype.card K.ι ≤ i + 1) : Subsingleton (F.HSucc K i) := by
  haveI := subsingleton_cochain F K h
  infer_instance

theorem cechFinrank_eq_zero [Nontrivial R] {i : ℕ} (h : Fintype.card K.ι ≤ i) : F.cechFinrank K i = 0 := by
  cases i with
  | zero =>
    haveI := subsingleton_H0 F K (Nat.le_zero.mp h)
    exact Module.finrank_zero_of_subsingleton
  | succ j =>
    haveI := subsingleton_HSucc F K h
    exact Module.finrank_zero_of_subsingleton

theorem eulerChar_eq_sum_range [Nontrivial R] {N : ℕ} (h : Fintype.card K.ι ≤ N) :
    F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ) := by
  rw [OModulePresheaf.eulerChar_def]
  refine Finset.sum_subset (Finset.range_mono h) fun i _ hi => ?_
  rw [Finset.mem_range, not_lt] at hi
  rw [cechFinrank_eq_zero F K hi, Nat.cast_zero, mul_zero]

theorem main :
    (∀ i : ℕ, Fintype.card K.ι ≤ i → IsEmpty (K.Idx i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i → Subsingleton (F.cochain K i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i + 1 → Subsingleton (F.HSucc K i)) ∧
    (Nontrivial R →
      (∀ i : ℕ, Fintype.card K.ι ≤ i → F.cechFinrank K i = 0) ∧
      (∀ N : ℕ, Fintype.card K.ι ≤ N →
        F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ))) :=
  ⟨fun _ h => isEmpty_idx K h, fun _ h => subsingleton_cochain F K h, fun _ h => subsingleton_HSucc F K h,
    fun _ => ⟨fun _ h => cechFinrank_eq_zero F K h, fun _ h => eulerChar_eq_sum_range F K h⟩⟩

end P2mVan

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) :
    (∀ i : ℕ, Fintype.card K.ι ≤ i → IsEmpty (K.Idx i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i → Subsingleton (F.cochain K i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i + 1 → Subsingleton (F.HSucc K i)) ∧
    (Nontrivial R →
      (∀ i : ℕ, Fintype.card K.ι ≤ i → F.cechFinrank K i = 0) ∧
      (∀ N : ℕ, Fintype.card K.ι ≤ N →
        F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ))) :=
  P2mVan.main F K
end S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
