-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Limits.Approximation), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.Ring.Subalgebras
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Limits.Descent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType

/-!
# Noetherian models of finitely presented families over affine bases

A finitely presented morphism to an arbitrary affine scheme is the pullback
of a finitely presented morphism over a Noetherian affine scheme. The model
source need not be affine. The Noetherian base is constructed from a finitely
generated integer subalgebra of the original base's global sections.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A finitely presented family over an affine base has an actual Noetherian
finite-presentation model. No Noetherian hypothesis or chosen model is required
on the input; this statement does not assert descent of properness or flatness. -/
theorem Scheme.exists_isPullback_over_noetherian_of_finitePresentation
    {sourceScheme baseScheme : Scheme.{schemeUniverse}} [IsAffine baseScheme]
    (sourceMap : sourceScheme ⟶ baseScheme) [LocallyOfFinitePresentation sourceMap]
    [QuasiCompact sourceMap] [QuasiSeparated sourceMap] :
    ∃ (stageRing : CommRingCat.{schemeUniverse}) (_ : IsNoetherianRing stageRing)
      (stageScheme : Scheme.{schemeUniverse}) (stageMap : stageScheme ⟶ Spec stageRing)
      (_ : LocallyOfFinitePresentation stageMap) (_ : QuasiCompact stageMap)
      (_ : QuasiSeparated stageMap) (comparison : sourceScheme ⟶ stageScheme)
      (baseComparison : baseScheme ⟶ Spec stageRing),
      IsPullback comparison sourceMap stageMap baseComparison := by
  let ringDiagram := CommRingCat.fgSubalgebraDiagram Γ(baseScheme, ⊤)
  let ringCocone := CommRingCat.fgSubalgebraCocone Γ(baseScheme, ⊤)
  let diagram := ringDiagram.op ⋙ Scheme.Spec
  let specCone := Scheme.Spec.mapCone ringCocone.op
  have specLimit : IsLimit specCone := isLimitOfPreserves Scheme.Spec
    (CommRingCat.isColimitFgSubalgebraCocone Γ(baseScheme, ⊤)).op
  let cone := specCone.extend baseScheme.isoSpec.hom
  have limit : IsLimit cone := IsLimit.ofIsoLimit specLimit
    (Cone.extendIso specCone baseScheme.isoSpec.symm)
  haveI affineStages : ∀ index, IsAffine (diagram.obj index) := by
    intro index
    change IsAffine (Spec (ringDiagram.obj index.unop))
    infer_instance
  haveI affineTransitions : ∀ {sourceIndex targetIndex}
      (transition : sourceIndex ⟶ targetIndex), IsAffineHom (diagram.map transition) := by
    intro sourceIndex targetIndex transition
    change IsAffineHom (Scheme.Spec.map (ringDiagram.op.map transition))
    infer_instance
  haveI compactStages : ∀ index, CompactSpace (diagram.obj index) := fun index ↦ inferInstance
  haveI quasiSeparatedStages : ∀ index, QuasiSeparatedSpace (diagram.obj index) :=
    fun index ↦ inferInstance
  obtain ⟨stage, stageScheme, stageMap, stage_finitePresentation, stage_quasiCompact,
      stage_quasiSeparated, comparison, square⟩ :=
    Scheme.exists_isPullback_of_finitePresentation limit sourceMap
  refine ⟨.of stage.unop.1, ?_, stageScheme, stageMap, stage_finitePresentation,
    stage_quasiCompact, stage_quasiSeparated, comparison, cone.π.app stage, square⟩
  letI : Algebra.FiniteType ℤ stage.unop.1 :=
    (Subalgebra.fg_iff_finiteType _).mp stage.unop.2
  exact Algebra.FiniteType.isNoetherianRing ℤ stage.unop.1

end AlgebraicGeometry
