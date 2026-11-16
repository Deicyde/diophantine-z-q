/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk.lean
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
    notation, no macro and no elaborator. The source's
    `p2m_exact_reverting @_root_.P2MW.<S>.solution` is replaced by the ordinary application of the
    ported `solution`;
  * internal `import`s are retargeted to the ported modules;
  * file-level `set_option`s reproduce the source build environment (source lakefile.lean
    leanOptions: autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000,
    backward.isDefEq.respectTransparency.types false) together with
    backward.isDefEq.respectTransparency.instanceSearchTypes false, a Lean 4.35 option absent from
    the source's Lean 4.33.1 whose `false` value restores the 4.33.1 behaviour.
  * every `open` of a Mathlib namespace is written `_root_.<Namespace>`: inside the port
    namespace a bare `open N` resolves to `ZInQ.Contrib.CloudW03NeronSurj.FLT.N` whenever that
    namespace exists in the environment and then shadows Mathlib's root `N`, which is what the
    source's `r2nos_open_dual` shim worked around. Naming the root explicitly is the ordinary-Lean
    equivalent and is stable however the import graph grows.
Manual repairs: none.
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.P2M.Sol.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk {U S : Scheme.{u}} (f : U ⟶ S) [Smooth f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) :=
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk.solution
    f y

end ZInQ.Contrib.CloudW03NeronSurj.FLT
