/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedAffine.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 a396368fc9844a1af62cd3c7416a5de154927e74eebd6371f7d15e57a0feae60.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine; 2 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.RingTheory.GeometricallyConnected.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


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

@[expose] public section

open CommRingCat

namespace AlgebraicGeometry

universe u

/-- An affine scheme is geometrically connected over a field if and only if its coordinate
algebra is geometrically connected over that field. -/

public theorem geometricallyConnected_spec_iff (k A : Type u) [Field k] [CommRing A]
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
