/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 5 `p2m_*` command(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import(s) of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Compat.PresheafOfModulesMonoidal` added (re-provides, under the port prefix, db584 API this file's source relies on and Mathlib 56a removed or moved).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.IsInvertible"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules Modules.IsLocallyFreeOfRank Modules.IsInvertible"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "IsLocallyFreeOfRank IsInvertible"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace RankOne
r2nos_namespace_dual

noncomputable def freeOneIsoUnit (Y : Scheme.{u}) :
    (SheafOfModules.free.{u} (ULift.{u} (Fin 1)) : Y.Modules) ≅ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) :=
  Limits.coproductUniqueIso (fun _ : ULift.{u} (Fin 1) => (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))

theorem iff (X : Scheme.{u}) (M : X.Modules) : IsLocallyFreeOfRank 1 M ↔ IsInvertible M := by
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, ⟨e⟩⟩ := h.exists_trivialization x
    exact ⟨U, hxU, ⟨e ≪≫ freeOneIsoUnit U.toScheme⟩⟩
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, ⟨e⟩⟩ := h.exists_trivialization x
    exact ⟨U, hxU, ⟨e ≪≫ (freeOneIsoUnit U.toScheme).symm⟩⟩

end RankOne

end AlgebraicGeometry.Scheme.Modules

theorem solution {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.IsLocallyFreeOfRank 1 M ↔ Scheme.Modules.IsInvertible M :=
  AlgebraicGeometry.Scheme.Modules.RankOne.iff X M

end S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
