/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 10 `p2m_*` command(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import(s) of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Compat.PresheafOfModulesMonoidal` added (re-provides, under the port prefix, db584 API this file's source relies on and Mathlib 56a removed or moved).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "morphismRestrict_ι Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules.pullbackCongr Modules Opens Modules.pullbackComp Modules.IsLocallyFreeOfRank"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr pullbackComp IsLocallyFreeOfRank"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

scoped instance opensMap_final_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

namespace IsLocallyFreeOfRank w03_export "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" "exists_trivialization" end IsLocallyFreeOfRank
r2nos_open_scoped "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" in
theorem IsLocallyFreeOfRank.pullback' {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : IsLocallyFreeOfRank n E) :
    IsLocallyFreeOfRank n ((Modules.pullback ψ).obj E) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, ⟨eU⟩⟩ := hE.exists_trivialization (ψ.base x)
  refine ⟨ψ ⁻¹ᵁ U, hU, ⟨?_⟩⟩
  have hfact : (ψ ⁻¹ᵁ U).ι ≫ ψ = (ψ ∣_ U) ≫ U.ι := (morphismRestrict_ι ψ U).symm
  exact (Modules.pullbackComp _ _).app E ≪≫ (Modules.pullbackCongr hfact).app E ≪≫
    ((Modules.pullbackComp _ _).app E).symm ≪≫ (Modules.pullback (ψ ∣_ U)).mapIso eU ≪≫
    pullbackFreeIso (ψ ∣_ U) (ULift.{u} (Fin n))

end AlgebraicGeometry.Scheme.Modules
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry"

theorem solution
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback ψ).obj E) :=
  AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback' ψ hE

end S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
