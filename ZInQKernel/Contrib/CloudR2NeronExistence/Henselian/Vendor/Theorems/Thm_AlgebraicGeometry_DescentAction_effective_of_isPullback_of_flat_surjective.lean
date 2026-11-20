import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective.lean
Original Git blob: 6b17f4d2c3ffb9f71cbe5afb7a0bc1228b810015
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_DescentAction
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
/- Source package leanOptions restored for this direct compiler leaf; no config edit. -/
set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
    {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x')
    {Y : Scheme.{u}} (p : X' ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    (w : pullback.fst (x' ≫ s) s ≫ p = A.act ≫ p)
    (hR : IsPullback (pullback.fst (x' ≫ s) s) A.act p p)
    (f : Y ⟶ S) (hpf : p ≫ f = x' ≫ s) :
    ∃ (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s),
      e.inv = pullback.lift p x' hpf ∧
      pullback.map (pullback.snd f s ≫ s) s (x' ≫ s) s e.hom (𝟙 S') (𝟙 S)
          (by rw [Category.comp_id, ← Category.assoc, he]) (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical s f).act ≫ e.hom := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
