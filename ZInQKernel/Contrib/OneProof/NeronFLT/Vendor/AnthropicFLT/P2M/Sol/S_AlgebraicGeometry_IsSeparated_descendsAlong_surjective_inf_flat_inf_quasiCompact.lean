/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective IsClosedImmersion.of_isPreimmersion UniversallyClosed QuasiCompact Scheme Flat IsClosedImmersion IsSeparated"
namespace IsSeparatedDescentAux
p2m_open "AlgebraicGeometry"

theorem isSeparated_iff_universallyClosed_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
  refine ⟨fun _ => inferInstance, fun _ => ⟨?_⟩⟩
  exact IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [MorphismProperty.diagonal_iff]
  exact isSeparated_iff_universallyClosed_diagonal f

end AlgebraicGeometry.IsSeparatedDescentAux

theorem solution :
    DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [AlgebraicGeometry.IsSeparatedDescentAux.isSeparated_eq_diagonal_universallyClosed]
  infer_instance
