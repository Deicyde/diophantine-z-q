/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean
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
Manual repairs:
  * the base ring `R` of `solution` occurs only in its instance hypotheses, never in its
    conclusion `Algebra.Etale S T`, so the ordinary application of `solution` leaves `R` a
    metavariable and instance search reports "typeclass instance problem is stuck". `R` is
    therefore supplied by name, `solution (R := R) n`, exactly as the source's own proof supplies
    it to this declaration's body
    (`R1NeronObjE2.etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (R := R) n`).
    The statement is unchanged.
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.P2M.Sol.S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

theorem Algebra.Etale.of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T :=
  _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.solution
    (R := R) n

end ZInQ.Contrib.CloudW03NeronSurj.FLT
