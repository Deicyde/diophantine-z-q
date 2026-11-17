import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem.lean
Original Git blob: 9069e5dc8db5b450ba6b6aad25c819de1bdd3507
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem NeronModelInfra.exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : (pullback f f).Opens)
    (hZ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Z)
    (ξ : X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ) :
    ∃ N : X.Opens, ξ ∈ N ∧ ∀ a : X, a ∈ N → f.base a = IsLocalRing.closedPoint R →
      Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = a} → ↑(pullback f f)) ⁻¹'
        (Z : Set ↑(pullback f f))) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_mem_opens_forall_dense_preimage_fst_of_forall_maximal_mem.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
