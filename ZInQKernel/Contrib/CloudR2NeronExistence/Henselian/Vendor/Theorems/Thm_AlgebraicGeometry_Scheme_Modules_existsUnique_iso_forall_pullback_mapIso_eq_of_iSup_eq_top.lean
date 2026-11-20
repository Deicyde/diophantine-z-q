import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.lean
Original Git blob: e9b0ea9302c225d383b303a5791402f6ae9ab886
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hB : ∀ i j, U i ⊓ U j ≤ ⨆ (k : {k : ι // U k ≤ U i ⊓ U j}), U k.1)
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ (Scheme.Modules.pullback (U i).ι).obj N)
    (he : ∀ (i j : ι) (h : U j ≤ U i),
      (Scheme.Modules.pullback (X.homOfLE h)).mapIso (e i) =
        ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app M ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app M) ≪≫
          e j ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app N ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app N).symm) :
    ∃! f : M ≅ N, ∀ i, (Scheme.Modules.pullback (U i).ι).mapIso f = e i := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
