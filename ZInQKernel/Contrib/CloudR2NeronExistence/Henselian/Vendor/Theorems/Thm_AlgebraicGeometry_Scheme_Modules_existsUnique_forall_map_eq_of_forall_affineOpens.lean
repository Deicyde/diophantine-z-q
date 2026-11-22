import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens.lean
Original Git blob: a061b5c8e8f2b0fd7722824434ea4e924f003754
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens

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

universe u

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_forall_map_eq_of_forall_affineOpens
    {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (s : ∀ U : X.affineOpens, (U : X.Opens) ≤ W → Γ(M, U))
    (hs : ∀ (U V : X.affineOpens) (hU : (U : X.Opens) ≤ W) (hVU : (V : X.Opens) ≤ U),
      M.presheaf.map (homOfLE hVU).op (s U hU) = s V (hVU.trans hU)) :
    ∃! t : Γ(M, W), ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W),
      M.presheaf.map (homOfLE hU).op t = s U hU := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
