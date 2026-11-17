/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsDiscreteValuationRing (X.presheaf.stalk (p.base (IsLocalRing.closedPoint k))) := by
  apply AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id _ _ hp
  have h := p.isClosedEmbedding.isClosed_range
  have hr : Set.range p.base = {p.base (IsLocalRing.closedPoint k)} :=
    Set.range_eq_singleton_iff.mpr fun y => congrArg p.base (Subsingleton.elim _ _)
  rwa [hr] at h
