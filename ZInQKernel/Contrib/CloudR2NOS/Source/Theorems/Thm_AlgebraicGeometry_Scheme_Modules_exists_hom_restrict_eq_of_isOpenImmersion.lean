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
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.lean
  Source sha256  : fb236762557bfe41f13b70c1f1b5105ae0758e2c86acae0c83fda51b5713ff2f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

theorem AlgebraicGeometry.Scheme.Modules.exists_hom_restrict_eq_of_isOpenImmersion
    {X Y₀ Y₁ Y₀₁ : Scheme.{u}} (f₀ : Y₀ ⟶ X) (f₁ : Y₁ ⟶ X) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
    (g₀ : Y₀₁ ⟶ Y₀) (g₁ : Y₀₁ ⟶ Y₁) [IsOpenImmersion g₀] [IsOpenImmersion g₁]
    (hg : g₀ ≫ f₀ = g₁ ≫ f₁) (hcov : f₀.opensRange ⊔ f₁.opensRange = ⊤)
    (hov : f₀.opensRange ⊓ f₁.opensRange ≤ (g₀ ≫ f₀).opensRange)
    {M N : X.Modules} (ψ₀ : M.restrict f₀ ⟶ N.restrict f₀) (ψ₁ : M.restrict f₁ ⟶ N.restrict f₁)
    (hψ : (Scheme.Modules.restrictFunctorComp g₀ f₀).hom.app M ≫ (Scheme.Modules.restrictFunctor g₀).map ψ₀ ≫
            (Scheme.Modules.restrictFunctorComp g₀ f₀).inv.app N =
          (Scheme.Modules.restrictFunctorCongr hg).hom.app M ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).hom.app M ≫ (Scheme.Modules.restrictFunctor g₁).map ψ₁ ≫
            (Scheme.Modules.restrictFunctorComp g₁ f₁).inv.app N ≫ (Scheme.Modules.restrictFunctorCongr hg).inv.app N) :
    ∃ φ : M ⟶ N, (Scheme.Modules.restrictFunctor f₀).map φ = ψ₀ ∧ (Scheme.Modules.restrictFunctor f₁).map φ = ψ₁ := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
