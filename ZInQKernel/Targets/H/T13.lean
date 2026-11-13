import Mathlib

/-!
# First H batch: T13, Skolem–Noether

Proposed closed target, reserved provider `ZInQ.Contrib.H.T13_holds`.
This registration draft is not mathematical or protected Astra acceptance.

The statement body preserves PR #41's `ZInQ.Targets.H.T13` at
`2757349fbd8ca613340b679bbd149f78c2baba6b`, from `HSyn.SkolemNoether`
in the frozen reference `Leaves.lean` at `48b5f075e5509678c84685f0d1ec53febd10b1e5`.
Reference file SHA-256: `99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`.

Crucial convention: the ambient algebra A is central simple; B is merely simple,
not assumed central. The automorphism-only case is not a substitute for this
embedding theorem. No separability, characteristic or map-surjectivity hypothesis
is added. One unit conjugates both maps on every element of B.

Reference locator: Reiner, Maximal Orders, Theorem 7.21 (publication locator still
subject to source review). A complete formal proof is proposed separately in
https://github.com/elliotglazer/diophantine-z-q/pull/42; it is not imported here.
This file needs no custom HSyn definitions: all objects are Mathlib objects.
-/

namespace ZInQ.Targets.H

/-- Exact full Skolem–Noether embedding statement, ambient-central convention. -/
def T13 : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

end ZInQ.Targets.H
