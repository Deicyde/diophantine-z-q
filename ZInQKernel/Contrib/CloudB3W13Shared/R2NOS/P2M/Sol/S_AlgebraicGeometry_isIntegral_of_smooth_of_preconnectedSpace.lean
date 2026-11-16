/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace.lean
  Retrieved      : 2026-11-16 (immutable raw blob at the revision above; bytes and sha256 in
                   `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/PORT_MANIFEST.md`)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(Cloud Batch 3 Worker 13 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
2026-11-16). The changes are mechanical; no statement, hypothesis, definition or proof term was
weakened or omitted unless listed under "manual repairs":
  * the whole file is wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end`, so the
    source's root declarations become `ZInQ.Contrib.CloudW03NeronSurj.FLT.<name>`;
  * the source's `import P2M.Util` is dropped: this port contains no port commands, no local
    notation, no macro and no elaborator;
  * internal `import`s are retargeted to the ported modules
    (`Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk` and
    `Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk`
    to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*`, `Theorems.Thm_IsRegularLocalRing_isDomain`
    to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*`);
  * references to ported declarations of other modules, and the `attribute [-simp]` target, are
    written with their full `ZInQ.Contrib.CloudW03NeronSurj.FLT.` names, since the port prefix is
    not opened here;
  * file-level `set_option`s reproduce the source build environment (source lakefile.lean
    leanOptions: autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000,
    backward.isDefEq.respectTransparency.types false) together with
    backward.isDefEq.respectTransparency.instanceSearchTypes false, a Lean 4.35 option absent from
    the source's Lean 4.33.1 whose `false` value restores the 4.33.1 behaviour;
  * scopes the source leaves open at end of file are closed explicitly (no-op).
  * every `open` of a Mathlib namespace is written `_root_.<Namespace>`: inside the port
    namespace a bare `open N` resolves to `ZInQ.Contrib.CloudW03NeronSurj.FLT.N` whenever that
    namespace exists in the environment and then shadows Mathlib's root `N`, which is what the
    source's `r2nos_open_dual` shim worked around. Naming the root explicitly is the ordinary-Lean
    equivalent and is stable however the import graph grows.
Manual repairs: none.
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_IsRegularLocalRing_isDomain

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

attribute [-simp] ZInQ.Contrib.CloudW03NeronSurj.FLT.RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace

universe u

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] [PreconnectedSpace X] [Nonempty X] : IsIntegral X := by
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : ConnectedSpace X := { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  exact _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk X
    fun x => by
      haveI := _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
      exact _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.IsRegularLocalRing.isDomain _

end P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace

end ZInQ.Contrib.CloudW03NeronSurj.FLT
