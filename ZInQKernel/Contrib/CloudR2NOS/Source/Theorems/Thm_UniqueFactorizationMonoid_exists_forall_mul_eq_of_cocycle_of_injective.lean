/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective.lean
  Source sha256  : 058af3c98a509ebddbbd1cd9ede28b45b12e867a00ef4264d0f22b5178687c80
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

theorem UniqueFactorizationMonoid.exists_forall_mul_eq_of_cocycle_of_injective
    {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    {K : Type*} [Field K] (φ : B →+* K) (hφ : Function.Injective φ)
    {ι : Type*} (b : ι → B) (u : ι → ι → K)
    (hreg : ∀ i j, b i ≠ 0 → b j ≠ 0 → ∃ (n : ℕ) (x : B), u i j * φ (b i * b j) ^ n = φ x)
    (hrefl : ∀ i, b i ≠ 0 → u i i = 1)
    (hcocycle : ∀ i j k, b i ≠ 0 → b j ≠ 0 → b k ≠ 0 → u i j * u j k = u i k) :
    ∃ h : ι → K, (∀ i, b i ≠ 0 →
        h i ≠ 0 ∧ (∃ (n : ℕ) (x : B), h i * φ (b i) ^ n = φ x) ∧
          (∃ (n : ℕ) (y : B), (h i)⁻¹ * φ (b i) ^ n = φ y)) ∧
      ∀ i j, b i ≠ 0 → b j ≠ 0 → u i j * h j = h i := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_UniqueFactorizationMonoid_exists_forall_mul_eq_of_cocycle_of_injective.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
