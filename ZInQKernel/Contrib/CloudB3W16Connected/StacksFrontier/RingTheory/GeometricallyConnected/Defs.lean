/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksFrontier/RingTheory/GeometricallyConnected/Defs.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
Broad unrelated Mathlib imports replaced by spectrum and algebraic tensor-product definitions.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksFrontier.RingTheory.GeometricallyConnected.Defs`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 54e6811ef1e4fc764abcdd0e5d61f17d7803f60a560234c8770e2d68f1996f20.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.RingTheory.GeometricallyConnected.Defs; 0 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module


public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


@[expose] public section

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

@[expose] public section

open scoped TensorProduct

namespace Algebra

/-- A `k`-algebra `S` over a field `k` is *geometrically connected over `k`* if for every field
extension `K/k` the spectrum of `K ⊗[k] S` is connected. -/

public class IsGeometricallyConnected (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  /-- For every field extension `K/k`, the spectrum of `K ⊗[k] S` is a connected space. -/
  connectedSpace_primeSpectrum_tensorProduct (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] S))

end Algebra

end
