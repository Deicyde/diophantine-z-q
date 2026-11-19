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
  Source file    : P2M/Sol/S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens.lean
  Source sha256  : 76e2f117f1b2e9327c7311158001d0a6d4e43744f57533092f38767e9d2e7f27
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace"

universe u

theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] [IsIntegral X] [IsIntegral Y]
    (U : X.Opens) (U' : Y.Opens) (hU : (U : Set X).Nonempty) (e : (U : Scheme.{u}) ≅ (U' : Scheme.{u})) :
    topologicalKrullDim ↥X = topologicalKrullDim ↥Y := by

  obtain ⟨x, hx⟩ := hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (U : Scheme.{u}).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (⟨x, hx⟩ : ↥U))
      isOpen_univ

  have hVX : IsAffineOpen (U.ι ''ᵁ V) := hV.image_of_isOpenImmersion U.ι
  have hVU' : IsAffineOpen (e.hom ''ᵁ V) := hV.image_of_isOpenImmersion e.hom
  have hVY : IsAffineOpen (U'.ι ''ᵁ (e.hom ''ᵁ V)) := hVU'.image_of_isOpenImmersion U'.ι
  have hneX : ((U.ι ''ᵁ V : X.Opens) : Set X).Nonempty := ⟨_, ⟨_, hxV, rfl⟩⟩
  have hneY : ((U'.ι ''ᵁ (e.hom ''ᵁ V) : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ⟨e.hom ⟨x, hx⟩, ⟨_, hxV, rfl⟩, rfl⟩⟩

  let ε : Γ(X, U.ι ''ᵁ V) ≅ Γ(Y, U'.ι ''ᵁ (e.hom ''ᵁ V)) :=
    U.ι.appIso V ≪≫ (e.hom.appIso V).symm ≪≫ (U'.ι.appIso _).symm
  rw [AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral fX hVX hneX,
    AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral fY hVY hneY]
  exact ringKrullDim_eq_of_ringEquiv ε.commRingCatIsoToRingEquiv
end S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
