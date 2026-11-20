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
  Source file    : Theorems/Thm_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one.lean
  Source sha256  : de2d059dd99668b58fa53797e96d88041611f5b028053da4f00d81f5d8c9d4cf
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
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace"

universe u

theorem AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [IsIntegral X] [LocallyOfFiniteType fX] [QuasiCompact fX] [IsIntegral Y] [IsProper fY]
    (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (hα : α ≫ fY = U.ι ≫ fX) (hdom : DenseRange α.base)
    (z : X) (hzU : z ∈ U) (hz₁ : ringKrullDim (X.presheaf.stalk z) = 1)
    (hzn : IsIntegrallyClosed (X.presheaf.stalk z))
    (hnd : ringKrullDim (Y.presheaf.stalk (α.base ⟨z, hzU⟩)) ≠ 0) :
    ∃ (O : ValuationSubring Y.functionField) (_ : O ≠ ⊤) (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap O Y.functionField)) ≫ ℓ₀ = Y.fromSpecStalk (genericPoint Y))
      (d : ℕ) (_ : ((d + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim Y)
      (g : Fin d → Y.functionField) (_ : ∀ i, g i ∈ O)
      (_ : ∀ Q : MvPolynomial (Fin d) k,
        O.valuation (Q.eval₂ ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom.comp
          (fY.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)) g) < 1 → Q = 0)
      (φ : CommRingCat.of O ⟶ X.presheaf.stalk z),
      IsLocalHom φ.hom ∧ Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
