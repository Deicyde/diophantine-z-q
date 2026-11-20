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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion.lean
  Source sha256  : bb19125bf481bed6dbdcde483f18c747e543fcce3fe50050a53ebb24f7443ee3
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 8 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion
r2nos_namespace_dual
r2nos_erase_attr "instance" "SheafOfModules.isIso_ihomModelToIhom"
r2nos_erase_attr "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    Nonempty ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F ≅
      (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)) := by
  haveI : IsIso (Scheme.Modules.projectionMorphism i F) :=
    Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map _ (fun x => by
      obtain ⟨U, hx, ⟨e⟩⟩ := hF.exists_trivialization x
      exact ⟨U, hx, (Scheme.Modules.isIso_pullback_map_projectionMorphism_iff i F U).mpr
        (Scheme.Modules.isIso_projectionMorphism_of_iso_free (i ∣_ U) _ e)⟩)
  exact ⟨asIso (Scheme.Modules.projectionMorphism i F)⟩
end S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_unit_tensor_iso_pushforward_pullback_of_isClosedImmersion
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
