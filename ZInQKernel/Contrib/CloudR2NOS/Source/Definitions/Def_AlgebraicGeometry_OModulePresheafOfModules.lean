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
  Source file    : Definitions/Def_AlgebraicGeometry_OModulePresheafOfModules.lean
  Source sha256  : 26ed56658a8a51fee824f6d6f25ccf2977a6ce502f445428218974c346f8c7e5
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
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite
r2nos_open_dual "CategoryTheory Opposite"

namespace AlgebraicGeometry.OModulePresheaf
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)

def ofModules : OModulePresheaf π where
  obj U := Γ(M, U)
  addCommGroup _ := inferInstance
  module U := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
  moduleSections _ := inferInstance
  isScalarTower U := Scheme.TwoAffineOpenCover.isScalarTower_sections π M U
  res h := Scheme.TwoAffineOpenCover.restrictSections π M h
  res_smul h a x := Scheme.Modules.map_smul M (homOfLE h) a x
  res_refl U := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (le_refl U)).op x = x
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), M.presheaf.map_id]
    rfl
  res_comp {U U' U''} h h' := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M U''
    refine LinearMap.ext fun x => ?_
    show M.presheaf.map (homOfLE (h.trans h')).op x
      = M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x)
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

theorem ofModules_obj (U : V.Opens) : (ofModules π M).obj U = Γ(M, U) := rfl

theorem ofModules_res_apply {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) :
    (ofModules π M).res h (show (ofModules π M).obj U' from x) = M.presheaf.map (homOfLE h).op x :=
  rfl

theorem ofModules_smul (U : V.Opens) (a : Γ(V, U)) (x : Γ(M, U)) :
    (show (ofModules π M).obj U from a • x) = a • (show (ofModules π M).obj U from x) := rfl

theorem ofModules_algebraMap_smul (U : V.Opens) (r : R) (x : (ofModules π M).obj U) :
    r • x = (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r • x :=
  rfl

theorem ofModules_twoChartSections (𝒱 : V.TwoAffineOpenCover) :
    (ofModules π M).twoChartSections 𝒱 = 𝒱.sectionsOf π M := rfl

end AlgebraicGeometry.OModulePresheaf

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
