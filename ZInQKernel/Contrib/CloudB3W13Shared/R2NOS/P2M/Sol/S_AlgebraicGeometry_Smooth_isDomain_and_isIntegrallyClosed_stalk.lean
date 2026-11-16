/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk.lean
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
    notation, no macro and no elaborator. Each source `p2m_*` command is replaced by the ordinary
    Lean it abbreviated (`p2m_open` by `open`, `p2m_exact_reverting @X` by the application of `X`);
  * internal `import`s are retargeted to the ported modules;
  * references to ported declarations of other modules are written with their full
    `ZInQ.Contrib.CloudW03NeronSurj.FLT.` names, since the port prefix is not opened here;
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
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem solution {U S : Scheme.{u}} (f : U ⟶ S) [Smooth f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) := by

  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := U) (x := y) (U := ⊤) trivial

  have hle : W ≤ f ⁻¹ᵁ ⊤ := by simp
  letI : Algebra Γ(S, ⊤) Γ(U, W) := (f.appLE ⊤ W hle).hom.toAlgebra
  haveI : Algebra.Smooth Γ(S, ⊤) Γ(U, W) := Smooth.smooth_appLE f (isAffineOpen_top S) hW hle

  letI : Algebra Γ(U, W) (U.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, hyW⟩ : W)
  haveI : IsLocalization.AtPrime (U.presheaf.stalk y) (hW.primeIdealOf ⟨y, hyW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hyW⟩
  exact _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
    Γ(S, ⊤) Γ(U, W) (hW.primeIdealOf ⟨y, hyW⟩).asIdeal (U.presheaf.stalk y)

end P2MW.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk

end ZInQ.Contrib.CloudW03NeronSurj.FLT
