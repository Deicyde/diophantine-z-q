import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.RingTheory.GeometricallyConnected.Defs`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory




universe u v

/-! # Geometrically connected algebras

Let `k` be a field and let `S` be a `k`-algebra. Then `S` is *geometrically connected over `k`*
if for every field extension `K/k` the spectrum of `K ⊗[k] S` is connected, i.e. is nonempty and
is not the disjoint union of two nonempty open and closed subsets. Taking `K = k` shows that the
spectrum of a geometrically connected algebra is itself connected, and the condition is strictly
stronger: `ℂ` is a field, so `Spec ℂ` is a point, but `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` has a two-point
spectrum, so `ℂ` is not geometrically connected over `ℝ`.

## Main definitions

* `Algebra.IsGeometricallyConnected`: the `k`-algebra `S` is geometrically connected over the
  field `k`, that is, `PrimeSpectrum (K ⊗[k] S)` is a connected space for every field extension
  `K/k` in the universe of `k`.

## References

* [Stacks 037T](https://stacks.math.columbia.edu/tag/037T)
-/


open scoped TensorProduct

namespace Algebra
#cloudR2LocalInstances
#cloudR2Vendor IsGeometricallyConnected in

/-- A `k`-algebra `S` over a field `k` is *geometrically connected over `k`* if for every field
extension `K/k` the spectrum of `K ⊗[k] S` is connected. -/

class IsGeometricallyConnected (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  /-- For every field extension `K/k`, the spectrum of `K ⊗[k] S` is a connected space. -/
  connectedSpace_primeSpectrum_tensorProduct (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] S))

end Algebra


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
