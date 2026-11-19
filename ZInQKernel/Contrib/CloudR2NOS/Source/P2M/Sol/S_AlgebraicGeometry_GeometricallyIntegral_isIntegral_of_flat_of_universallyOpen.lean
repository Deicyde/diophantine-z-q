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
  Source file    : P2M/Sol/S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen.lean
  Source sha256  : e309fa45c807683b21c924f3a6882873fa331449de4e3c57cd5ac9acebbb26a0
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
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

namespace P2MW.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
r2nos_namespace_dual

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "GeometricallyReduced GeometricallyIntegral GeometricallyIntegral.isIntegral_of_isLocallyNoetherian GeometricallyIrreducible IsIntegral GeometricallyIrreducible.irreducibleSpace Scheme UniversallyOpen isIntegral_iff_irreducibleSpace_and_isReduced Flat GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents"
w03_open "AlgebraicGeometry"

theorem finite_irreducibleComponents_of_irreducibleSpace (S : Type*) [TopologicalSpace S]
    [IrreducibleSpace S] : (irreducibleComponents S).Finite := by
  refine (Set.finite_singleton (Set.univ : Set S)).subset ?_
  intro Z hZ
  rw [Set.mem_singleton_iff]
  exact hZ.eq_of_le (IrreducibleSpace.isIrreducible_univ S) (Set.subset_univ Z)

end AlgebraicGeometry

theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] : IsIntegral X := by
  have : Finite (irreducibleComponents S) :=
    (AlgebraicGeometry.finite_irreducibleComponents_of_irreducibleSpace S).to_subtype
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents f⟩
end S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
