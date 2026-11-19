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
  Source file    : Definitions/Def_AlgebraicGeometry_IdealSheafModuleMaps.lean
  Source sha256  : cf2cea140b3b15164266801a38a00325022eda97508a4ab7fc697f35be6ffad9
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
r2nos_open_dual "CategoryTheory CategoryTheory.Limits"

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData
r2nos_namespace_dual

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData)

open Opposite
r2nos_open_dual "Opposite"

abbrev comapSubschemeHom : (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι

@[reassoc]
lemma comapSubschemeHom_comp :
    I.comapSubschemeHom f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  simp [comapSubschemeHom]

lemma kernelι_unitToPushforwardUnit_map_eq_zero :
    (kernel.ι I.subschemeι.unitToPushforwardUnit ≫ f.unitToPushforwardUnit) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map
        (I.comap f).subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m

  set s : Γ(X, U.unop) := (kernel.ι I.subschemeι.unitToPushforwardUnit).val.app U m with hs_def
  have hs : I.subschemeι.app U.unop s = 0 := by
    have := congrArg (fun φ ↦ φ.val.app U m) (kernel.condition I.subschemeι.unitToPushforwardUnit)
    exact this

  have hs' : (I.subschemeι.app U.unop).hom s = 0 := hs

  have h0 : ((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s = 0 := by
    change ((I.comapSubschemeHom f).app _).hom ((I.subschemeι.app U.unop).hom s) = 0
    rw [hs', map_zero]

  have key := congrArg (fun φ ↦ φ.hom s)
    (Scheme.Hom.congr_app (I.comapSubschemeHom_comp f).symm U.unop)
  change (((I.comap f).subschemeι ≫ f).app U.unop).hom s = 0
  rw [key]
  change ((I.comap f).subscheme.presheaf.map _).hom
    (((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s) = 0
  rw [h0, map_zero]

def moduleToPushforwardComapModule :
    (I.module : SheafOfModules X.ringCatSheaf) ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (I.comap f).module :=
  kernel.lift _ _ (I.kernelι_unitToPushforwardUnit_map_eq_zero f) ≫
    (PreservesKernel.iso (SheafOfModules.pushforward f.toRingCatSheafHom)
      (I.comap f).subschemeι.unitToPushforwardUnit).inv

def pullbackModuleComparison :
    (Scheme.Modules.pullback f).obj I.module ⟶ (I.comap f).module :=
  ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _).symm
    (I.moduleToPushforwardComapModule f)

end AlgebraicGeometry.Scheme.IdealSheafData

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
