/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (GeometricallyReduced GeometricallyIntegral GeometricallyIntegral.isIntegral_of_isLocallyNoetherian GeometricallyIrreducible IsIntegral GeometricallyIrreducible.irreducibleSpace Scheme UniversallyOpen isIntegral_iff_irreducibleSpace_and_isReduced Flat GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents)
open AlgebraicGeometry

theorem finite_irreducibleComponents_of_irreducibleSpace (S : Type*) [TopologicalSpace S]
    [IrreducibleSpace S] : (irreducibleComponents S).Finite := by
  refine (Set.finite_singleton (Set.univ : Set S)).subset ?_
  intro Z hZ
  rw [Set.mem_singleton_iff]
  exact hZ.eq_of_le (IrreducibleSpace.isIrreducible_univ S) (Set.subset_univ Z)

end AlgebraicGeometry

theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] : IsIntegral X := by
  have : Finite (irreducibleComponents S) :=
    (AlgebraicGeometry.finite_irreducibleComponents_of_irreducibleSpace S).to_subtype
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents f⟩
