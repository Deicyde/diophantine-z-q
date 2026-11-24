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
  Source file    : Theorems/Thm_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact.lean
  Source sha256  : 8009cd75b687233e7b82dba11d7cede66e8fe0d5bf3a99ce7456600106cc60de
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
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u v

theorem LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₁)] [FiniteDimensional k (B₁ ⧸ LinearMap.range d₁)]
    [FiniteDimensional k (LinearMap.ker d₃)] [FiniteDimensional k (B₃ ⧸ LinearMap.range d₃)] :
    FiniteDimensional k (LinearMap.ker d₂) ∧ FiniteDimensional k (B₂ ⧸ LinearMap.range d₂) ∧
    (Module.finrank k (LinearMap.ker d₂) : ℤ) - Module.finrank k (B₂ ⧸ LinearMap.range d₂)
      = ((Module.finrank k (LinearMap.ker d₁) : ℤ) - Module.finrank k (B₁ ⧸ LinearMap.range d₁))
        + ((Module.finrank k (LinearMap.ker d₃) : ℤ) - Module.finrank k (B₃ ⧸ LinearMap.range d₃)) := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
