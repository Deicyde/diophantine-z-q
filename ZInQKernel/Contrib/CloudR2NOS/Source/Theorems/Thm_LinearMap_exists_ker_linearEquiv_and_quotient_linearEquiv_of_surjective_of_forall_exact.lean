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
  Source file    : Theorems/Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.lean
  Source sha256  : 3c78565b53e97593a23d029b1d08c7b98e95596cc113b51742de80acdeeb121d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
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
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u v

theorem LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
    {R : Type u} [CommRing R] {C D : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (dC : ∀ n, C n →ₗ[R] C (n + 1)) (dD : ∀ n, D n →ₗ[R] D (n + 1)) (f : ∀ n, C n →ₗ[R] D n)
    (hf : ∀ (n : ℕ) (x : C n), f (n + 1) (dC n x) = dD n (f n x))
    (hdC : ∀ (n : ℕ) (x : C n), dC (n + 1) (dC n x) = 0)
    (hsurj : ∀ n, Function.Surjective (f n))
    (hex0 : ∀ x : C 0, f 0 x = 0 → dC 0 x = 0 → x = 0)
    (hexS : ∀ (n : ℕ) (x : C (n + 1)), f (n + 1) x = 0 → dC (n + 1) x = 0 →
      ∃ y : C n, f n y = 0 ∧ dC n y = x) :
    (∃ e : LinearMap.ker (dC 0) ≃ₗ[R] LinearMap.ker (dD 0), ∀ x : LinearMap.ker (dC 0), (e x : D 0) = f 0 x) ∧
    ∀ n : ℕ, ∃ e : (LinearMap.ker (dC (n + 1)) ⧸
        (LinearMap.range (dC n)).comap (LinearMap.ker (dC (n + 1))).subtype) ≃ₗ[R]
      (LinearMap.ker (dD (n + 1)) ⧸ (LinearMap.range (dD n)).comap (LinearMap.ker (dD (n + 1))).subtype),
      ∀ (x : LinearMap.ker (dC (n + 1))) (y : LinearMap.ker (dD (n + 1))), (y : D (n + 1)) = f (n + 1) x →
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
