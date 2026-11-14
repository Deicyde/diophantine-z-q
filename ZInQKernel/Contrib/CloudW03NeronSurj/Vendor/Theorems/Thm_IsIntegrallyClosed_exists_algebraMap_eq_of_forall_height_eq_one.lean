/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 2 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 `p2m_*` command(s) renamed to `w03_*`.
  * 1 `_root_.` reference(s) to source-specific namespaces qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.P2M.Sol.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

theorem IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, algebraMap R K r = x := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
