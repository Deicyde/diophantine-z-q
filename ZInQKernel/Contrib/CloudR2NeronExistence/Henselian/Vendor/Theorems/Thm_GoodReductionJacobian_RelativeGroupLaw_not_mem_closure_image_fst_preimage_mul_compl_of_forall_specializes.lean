import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes.lean
Original Git blob: d270d0067bb4158621c01fc036a635e6d3ad58b1
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
      ((LB.mul (pullback.snd g (B.fromSpecResidueField s₀ ≫ g) ≫ (B.fromSpecResidueField s₀ ≫ g))
          ⟨pullback.fst g (B.fromSpecResidueField s₀ ≫ g), pullback.condition⟩
          (schemeHomOverComp (pullback.snd g (B.fromSpecResidueField s₀ ≫ g)) rfl
            (⟨B.fromSpecResidueField s₀, rfl⟩ :
              SchemeHomOver (B.fromSpecResidueField s₀ ≫ g) g))).1.base ⁻¹' ((U : Set B)ᶜ))) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
