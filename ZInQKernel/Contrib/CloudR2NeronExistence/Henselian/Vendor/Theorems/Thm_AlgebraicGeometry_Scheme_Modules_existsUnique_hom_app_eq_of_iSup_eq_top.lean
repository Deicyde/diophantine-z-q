import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top.lean
Original Git blob: 701f6eca581946b45d9535d3a824dd3d1687b42f
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top

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

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (f : ∀ (W : X.Opens), (∃ i, W ≤ U i) → (Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W)))
    (hf : ∀ (W W' : X.Opens) (hW : ∃ i, W ≤ U i) (h : W' ≤ W) (x : Γ(M, W)),
      N.presheaf.map (homOfLE h).op (f W hW x) = f W' (hW.imp fun _ hi => h.trans hi) (M.presheaf.map (homOfLE h).op x)) :
    ∃! F : M ⟶ N, ∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : Γ(M, W)), F.app W x = f W hW x := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
