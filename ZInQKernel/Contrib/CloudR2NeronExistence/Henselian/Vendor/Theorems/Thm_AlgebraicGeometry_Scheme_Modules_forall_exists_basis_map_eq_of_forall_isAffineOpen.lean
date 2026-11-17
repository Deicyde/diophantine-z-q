import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen.lean
Original Git blob: 55fd079a55f845653b17496a8dbda3c201ac9341
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) {V : X.Opens} {d : ℕ} (e : Fin d → Γ(M, V))
    (he : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
