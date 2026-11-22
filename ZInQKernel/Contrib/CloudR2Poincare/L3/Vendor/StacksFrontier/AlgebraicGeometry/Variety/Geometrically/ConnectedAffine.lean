import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.GeometricallyConnected.Defs
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Geometric connectedness of an affine scheme

For a field `k` and a commutative `k`-algebra `A`, geometric connectedness of the affine
scheme `Spec A` over `Spec k` is equivalent to geometric connectedness of the algebra `A`.

## Main results

* `AlgebraicGeometry.geometricallyConnected_spec_iff` identifies the scheme-theoretic and
  algebraic notions of geometric connectedness for an affine scheme.

## References

* [Stacks Project, Tag 0386](https://stacks.math.columbia.edu/tag/0386)
-/


open CommRingCat

namespace AlgebraicGeometry
#cloudR2LocalInstances

universe u
#cloudR2Vendor geometricallyConnected_spec_iff in

/-- An affine scheme is geometrically connected over a field if and only if its coordinate
algebra is geometrically connected over that field. -/

theorem geometricallyConnected_spec_iff (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k A))) ↔
      Algebra.IsGeometricallyConnected k A := by
  rw [AlgebraicGeometry.geometricallyConnected_iff,
    AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine ⟨fun h ↦ ⟨fun K _ _ ↦ ?_⟩, fun h K _ _ ↦ ?_⟩
  · exact (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k A K).toRingEquiv).connectedSpace_iff.mp
      ((Scheme.homeoOfIso (pullbackSpecIso k A K)).connectedSpace_iff.mp (h K))
  · exact (Scheme.homeoOfIso (pullbackSpecIso k A K)).connectedSpace_iff.mpr
      ((PrimeSpectrum.homeomorphOfRingEquiv
        (Algebra.TensorProduct.comm k A K).toRingEquiv).connectedSpace_iff.mpr
        (h.connectedSpace_primeSpectrum_tensorProduct K))

end AlgebraicGeometry

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
