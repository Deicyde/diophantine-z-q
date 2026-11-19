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
  Source file    : Definitions/Def_AlgebraicGeometry_ModulesPushforwardRestrict.lean
  Source sha256  : 1a2b3f31d6551bb2297b6c0f1c8ab15d7802e56b0b37dd41dd5dbd0fd7fdcb31
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 400000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
r2nos_open_dual "CategoryTheory AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry.Scheme.Modules
r2nos_namespace_dual

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)

noncomputable def restrictPushforwardOpensIso :
    (Opens.map (g ∣_ W).base ⋙ (g ⁻¹ᵁ W).ι.opensFunctor : W.toScheme.Opens ⥤ X.Opens) ≅
      W.ι.opensFunctor ⋙ Opens.map g.base :=
  NatIso.ofComponents (fun U => eqToIso (image_morphismRestrict_preimage g W U))
    (fun _ => Subsingleton.elim _ _)


noncomputable def pushforwardRestrictIso :
    restrictFunctor (g ⁻¹ᵁ W).ι ⋙ pushforward (g ∣_ W) ≅ pushforward g ⋙ restrictFunctor W.ι :=
  letI := CategoryTheory.Functor.isContinuous_comp.{u} (Opens.map (g ∣_ W).base) (g ⁻¹ᵁ W).ι.opensFunctor
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology ↑(g ⁻¹ᵁ W)) (Opens.grothendieckTopology X)
  letI := CategoryTheory.Functor.isContinuous_comp.{u} W.ι.opensFunctor (Opens.map g.base)
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  by
    refine SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardNatIso _ (restrictPushforwardOpensIso g W).symm ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
    refine SheafOfModules.pushforwardCongr ?_
    ext U x
    simp only [Functor.sheafPushforwardContinuous_obj_obj_obj, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, Hom.toRingCatSheafHom, op_unop, Opens.ι_appIso, Iso.refl_inv,
      Functor.sheafPushforwardContinuousNatTrans, restrictPushforwardOpensIso, Iso.symm_hom, ObjectProperty.ι_obj,
      Category.assoc, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      TopCat.Presheaf.pushforward_obj_obj, Functor.sheafPushforwardContinuous_map_hom_app, Functor.op_obj,
      NatTrans.op_app, NatIso.ofComponents_inv_app, eqToIso.inv, eqToHom_op, Functor.comp_map, RingCat.hom_comp,
      CommRingCat.forgetToRingCat_map_hom]
    change (X.presheaf.map (eqToHom _)) ((g ∣_ W).app (unop U) x) = g.app (W.ι ''ᵁ unop U) x
    rw [morphismRestrict_app']
    erw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app]
    rfl

lemma pushforwardRestrictIso_hom_app_app (M : X.Modules) (U : W.toScheme.Opens) :
    ((pushforwardRestrictIso g W).hom.app M).app U =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage g W U).symm).op := by
  first
    | rfl
    | (ext x; simp [pushforwardRestrictIso, restrictPushforwardOpensIso, SheafOfModules.pushforwardCongr,
        SheafOfModules.pushforwardNatIso, SheafOfModules.pushforwardComp, eqToHom_op, Scheme.Modules.Hom.app])

end AlgebraicGeometry.Scheme.Modules

end ZInQ.Contrib.CloudW03NeronSurj.FLT
