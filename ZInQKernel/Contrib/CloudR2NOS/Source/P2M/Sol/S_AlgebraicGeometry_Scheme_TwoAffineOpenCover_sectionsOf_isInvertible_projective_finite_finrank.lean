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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank.lean
  Source sha256  : 9cb4759662b5afc5a4be4dc8383419893d8ec22e8362feab9fceb404aea13d1a
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 16000000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 7 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
r2nos_namespace_dual

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct"

set_option autoImplicit false

noncomputable section

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Module.Projective (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    Module.Finite (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0) = 1) ∧
    Module.Projective (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    Module.Finite (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1) = 1) ∧
    Module.Projective (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    Module.Finite (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A01 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A01] (𝒱.sectionsOf c M).M01) = 1) := by
  refine ⟨
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩ K fK algK,
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩ K fK algK,
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩ K fK algK⟩

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
