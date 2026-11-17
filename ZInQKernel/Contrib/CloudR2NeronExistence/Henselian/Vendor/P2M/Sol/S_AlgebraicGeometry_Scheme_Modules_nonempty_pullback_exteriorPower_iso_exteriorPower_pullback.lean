import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback.lean
Original Git blob: e47bb3daecab8d7662c8a2b338e40471f9e18e79
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Normalized 1 named/adjacent namespace closers for Lean 4.35.
* Explicitly closed 3 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_ModulesRestrictOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry
h77_bridge_namespace
h77_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.exteriorPower"
namespace Scheme
h77_bridge_namespace
h77_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Modules Opens PresheafOfModules Modules.exteriorPower"
namespace Modules
h77_bridge_namespace
h77_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf presheafExteriorPower exteriorPower restrictPresheaf restrictPresheaf₀ restrictPresheafIsoRestrictPresheaf₀ sheafificationCompPullbackIso restrictOpen restrictOpenIsoPullback"
h77_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

noncomputable def restrictPresheaf₀CompPresheafExteriorPowerIso (n : ℕ) (U : X.Opens) :
    presheafExteriorPower X n ⋙ restrictPresheaf₀ U ≅
      restrictPresheaf₀ U ⋙ presheafExteriorPower (U : Scheme.{u}) n :=
  NatIso.ofComponents
    (fun P => PresheafOfModules.isoMk (fun V => Iso.refl _) (fun V W f => by
      simp only [Iso.refl_hom, Category.id_comp]
      rfl))
    (fun φ => by
      ext V : 1
      simp only [Functor.comp_map, PresheafOfModules.isoMk_hom_app,
        Iso.refl_hom, PresheafOfModules.comp_app, Category.comp_id, Category.id_comp]
      rfl)

noncomputable def restrictPresheafCompPresheafExteriorPowerIso (n : ℕ) (U : X.Opens) :
    presheafExteriorPower X n ⋙ restrictPresheaf U ≅
      restrictPresheaf U ⋙ presheafExteriorPower (U : Scheme.{u}) n :=
  Functor.isoWhiskerLeft _ (restrictPresheafIsoRestrictPresheaf₀ U) ≪≫
    restrictPresheaf₀CompPresheafExteriorPowerIso n U ≪≫
    Functor.isoWhiskerRight (restrictPresheafIsoRestrictPresheaf₀ U).symm _

section steps
variable (n : ℕ) (U : X.Opens) (M : X.Modules)

noncomputable def pullbackExteriorPowerIso_step1 :
    (Modules.pullback U.ι).obj ((exteriorPower X n).obj M) ≅
      (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((restrictPresheaf U).obj ((presheafExteriorPower X n).obj M.val)) :=
  (sheafificationCompPullbackIso U).app ((presheafExteriorPower X n).obj M.val)

noncomputable def pullbackExteriorPowerIso_step2 :
    (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((restrictPresheaf U).obj ((presheafExteriorPower X n).obj M.val)) ≅
      (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafExteriorPower (U : Scheme.{u}) n).obj ((restrictPresheaf U).obj M.val)) :=
  (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).mapIso
    ((restrictPresheafCompPresheafExteriorPowerIso n U).app M.val)

noncomputable def pullbackExteriorPowerIso_step25 :
    (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafExteriorPower (U : Scheme.{u}) n).obj ((restrictPresheaf U).obj M.val)) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((restrictOpen U).obj M) :=
  Iso.refl _

noncomputable def pullbackExteriorPowerIso_step3 :
    (exteriorPower (U : Scheme.{u}) n).obj ((restrictOpen U).obj M) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((Modules.pullback U.ι).obj M) :=
  (exteriorPower (U : Scheme.{u}) n).mapIso ((restrictOpenIsoPullback U).app M)

end steps

noncomputable def pullbackExteriorPowerIso (n : ℕ) (U : X.Opens) (M : X.Modules) :
    (Modules.pullback U.ι).obj ((exteriorPower X n).obj M) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((Modules.pullback U.ι).obj M) :=
  pullbackExteriorPowerIso_step1 n U M ≪≫ pullbackExteriorPowerIso_step2 n U M ≪≫
    pullbackExteriorPowerIso_step25 n U M ≪≫ pullbackExteriorPowerIso_step3 n U M

end Modules
end Scheme
end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback.AlgebraicGeometry in
theorem solution {X : Scheme.{u}} (n : ℕ) (U : X.Opens) (M : X.Modules) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.exteriorPower X n).obj M) ≅
      (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).obj ((Scheme.Modules.pullback U.ι).obj M)) :=
  ⟨Scheme.Modules.pullbackExteriorPowerIso n U M⟩


end P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
