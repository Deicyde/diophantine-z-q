/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn.lean
  Source sha256  : db9de6dc2bcff2d9de9f82a079bd2bfab1cb37f1729715cf4971a880263be9dc
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.map_smul Scheme.Modules.IsFrameOn Scheme.Modules.UnitCocycle"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Γ Modules Opens Modules.map_smul restrict Modules.IsFrameOn Modules.UnitCocycle"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "presheaf restrict map_smul IsFrameOn UnitCocycle"
namespace RatioCocycle
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

w03_open "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle"

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_smul' {A B : X.Opens} (h : B ≤ A) (r : Γ(X, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (r • m) = X.presheaf.map (homOfLE h).op r • M.presheaf.map (homOfLE h).op m :=
  Scheme.Modules.map_smul M _ r m

theorem map_map {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op m) = M.presheaf.map (homOfLE (hCB.trans hBA)).op m := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

end AlgebraicGeometry.Scheme.Modules.RatioCocycle

open AlgebraicGeometry.Scheme.Modules.RatioCocycle AlgebraicGeometry.Scheme.Modules.GlueOfCocycle in
r2nos_open_dual "AlgebraicGeometry.Scheme.Modules.RatioCocycle AlgebraicGeometry.Scheme.Modules.GlueOfCocycle" in
theorem solution
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    {M : X.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (U i)) :
    ∃ c : Scheme.Modules.UnitCocycle U, ∀ i j,
      M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
        c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) := by
  classical

  have hcoef : ∀ i j, ∃! u : Γ(X, U i ⊓ U j),
      u • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) =
        M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) :=
    fun i j => (he i).existsUnique inf_le_left inf_le_left _
  choose u hu huniq using hcoef

  have hcoefW : ∀ (i : ι) {W : X.Opens} (hW : W ≤ U i) (a b : Γ(X, W)),
      a • M.presheaf.map (homOfLE hW).op (e i) = b • M.presheaf.map (homOfLE hW).op (e i) → a = b :=
    fun i W hW a b h => ((he i) hW hW).1 h
  refine ⟨⟨u, fun i => ?_, fun i j k => ?_⟩, fun i j => (hu i j).symm⟩
  ·
    apply hcoefW i inf_le_left
    rw [hu i i, one_smul]
  ·
    let T : X.Opens := U i ⊓ U j ⊓ U k
    have hTi : T ≤ U i := inf_le_left.trans inf_le_left
    have hTij : T ≤ U i ⊓ U j := le_inf hTi (inf_le_left.trans inf_le_right)
    have hTjk : T ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTik : T ≤ U i ⊓ U k := le_inf hTi inf_le_right
    apply hcoefW i hTi

    have hij := congrArg (M.presheaf.map (homOfLE hTij).op) (hu i j)
    have hjk := congrArg (M.presheaf.map (homOfLE hTjk).op) (hu j k)
    have hik := congrArg (M.presheaf.map (homOfLE hTik).op) (hu i k)
    rw [map_smul', map_map, map_map] at hij hjk hik
    show (rO hTij (u i j) * rO hTjk (u j k)) • _ = rO hTik (u i k) • _
    rw [mul_comm, mul_smul]
    erw [hij, hjk, hik]
end S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
