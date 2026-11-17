/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 1 `_root_.` reference(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 2 `attribute [-instance]`/`[-simp]` guard line(s) run through `r2nos_erase_attr` (identical erasure; a name absent at the fixed pins is reported, not fatal).
  * 1 `p2m_*` command(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import(s) of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (re-provides, under the port prefix, db584 API this file's source relies on and Mathlib 56a removed or moved).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

r2nos_erase_attr "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
r2nos_erase_attr "simp" "PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val"

universe u

open CategoryTheory
r2nos_open_dual "CategoryTheory"
theorem PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
    (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))).IsMonoidal := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.solution


end ZInQ.Contrib.CloudW03NeronSurj.FLT
