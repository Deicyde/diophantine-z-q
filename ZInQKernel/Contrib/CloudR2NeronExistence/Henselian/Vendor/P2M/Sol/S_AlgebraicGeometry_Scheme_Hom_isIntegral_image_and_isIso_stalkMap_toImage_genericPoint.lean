import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint.lean
Original Git blob: 11ed97a9e5841da1e92ceefcb4cf6e7ede1f3252
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {X P : Scheme.{u}} [IsIntegral X] (f : X ⟶ P) [IsImmersion f] [QuasiCompact f] :
    ∃ (_ : IsIntegral f.image),
      f.toImage.base (genericPoint X) = genericPoint f.image ∧
      IsIso (f.toImage.stalkMap (genericPoint X)) := by
  have hirr : IrreducibleSpace ↥f.image := by
    rw [irreducibleSpace_def]
    have h1 : IsIrreducible (Set.range ⇑f.toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
    have h2 := h1.closure
    rwa [f.toImage.denseRange.closure_range] at h2
  have hcov : ∀ U : P.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    have hq : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U) := by
      haveI : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ RingHom.ker (f.app U).hom) :=
        isReduced_of_injective (RingHom.kerLift (f.app U).hom) (RingHom.kerLift_injective _)
      exact isReduced_of_injective (Ideal.quotEquivOfEq (f.ker_apply U))
        (Ideal.quotEquivOfEq (f.ker_apply U)).injective
    show IsReduced (Spec (.of (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U)))
    infer_instance
  have hred : IsReduced f.image :=
    @IsReduced.of_openCover f.image f.ker.subschemeCover.openCover hcov
  haveI : IsIntegral f.image := isIntegral_of_irreducibleSpace_of_isReduced f.image
  exact ⟨this, genericPoint_eq_of_isOpenImmersion f.toImage, inferInstance⟩


end P2MW.S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
