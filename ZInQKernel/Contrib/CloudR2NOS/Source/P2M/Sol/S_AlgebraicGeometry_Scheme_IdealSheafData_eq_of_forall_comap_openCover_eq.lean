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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq.lean
  Source sha256  : ed90b83408303dc4fa9ff8a194d3b07360961c46d36ac2f76955cd3bee86aef6
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Cover.Open
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.IdealSheafData"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "OpenCover affineOpens isBasis_affineOpens Opens IdealSheafData Cover"
namespace IdealSheafData
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.IdealSheafData" "ideal ext_of_iSup_eq_top comap ideal_comap_of_isOpenImmersion"
w03_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem eq_of_forall_comap_openCover_eq_aux
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  refine ext_of_iSup_eq_top
    (fun p : Σ i, (𝒰.X i).affineOpens => ⟨𝒰.f p.1 ''ᵁ (p.2 : (𝒰.X p.1).Opens),
      p.2.2.image_of_isOpenImmersion _⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨y, hy⟩ := 𝒰.covers x
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      (𝒰.X (𝒰.idx x)).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨𝒰.idx x, ⟨W, hW⟩⟩, ⟨y, hyW, hy⟩⟩
  · rintro ⟨i, W⟩
    have hW := congrArg (fun K : (𝒰.X i).IdealSheafData => K.ideal W) (h i)
    simp only [ideal_comap_of_isOpenImmersion] at hW
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv).2 hW

end AlgebraicGeometry.Scheme.IdealSheafData

theorem solution
    {X : Scheme.{u}} (𝒰 : X.OpenCover) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J :=
  AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq_aux 𝒰 h
end S_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
