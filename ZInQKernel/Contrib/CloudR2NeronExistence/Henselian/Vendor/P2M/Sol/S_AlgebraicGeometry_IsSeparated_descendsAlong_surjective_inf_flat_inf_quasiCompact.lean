import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean
Original Git blob: 5038bdf70770e52f86428341710bb803859651f2
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Normalized 1 named/adjacent namespace closers for Lean 4.35.
* Explicitly closed 2 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

h77_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry"

namespace AlgebraicGeometry
h77_bridge_namespace
h77_export "AlgebraicGeometry" "Surjective IsClosedImmersion.of_isPreimmersion UniversallyClosed QuasiCompact Scheme Flat IsClosedImmersion IsSeparated"
namespace IsSeparatedDescentAux
h77_bridge_namespace
h77_open "AlgebraicGeometry"

theorem isSeparated_iff_universallyClosed_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
  refine ⟨fun _ => inferInstance, fun _ => ⟨?_⟩⟩
  exact IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [MorphismProperty.diagonal_iff]
  exact isSeparated_iff_universallyClosed_diagonal f

end IsSeparatedDescentAux
end AlgebraicGeometry

theorem solution :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [AlgebraicGeometry.IsSeparatedDescentAux.isSeparated_eq_diagonal_universallyClosed]
  infer_instance


end P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
