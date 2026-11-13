import Mathlib

/-!
# First H batch: T17, Kronecker–Weber

Proposed closed target, reserved provider `ZInQ.Contrib.H.T17_holds`.
This registration draft is not mathematical or protected Astra acceptance.

The statement body preserves PR #41's `ZInQ.Targets.H.T17` at
`2757349fbd8ca613340b679bbd149f78c2baba6b`, from `HSyn.KroneckerWeber`
in the frozen reference `Leaves.lean` at `48b5f075e5509678c84685f0d1ec53febd10b1e5`.
Reference file SHA-256: `99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`.

Reference locator: Washington, Introduction to Cyclotomic Fields, Theorem 14.1
(locator still unverified). A preliminary independent review opened Milne,
Class Field Theory v4.03, introduction page 6 and Chapter V Example 3.10 (page 159),
which state the finite abelian extension theorem used here.
The abstract finite Galois number field's
automorphisms commute; the conclusion supplies a Q-algebra embedding into one
positive-index cyclotomic field. A theorem only about a chosen concrete subfield
requires a checked embedding/transport derivation to supply this statement.
No assumed Kronecker–Weber premise or restricted Galois group is added.
All objects here are Mathlib objects; no custom HSyn definitions are needed.
The codomain uses the canonical Rat algebra. CyclotomicField.algebra agrees with
it, but instance-level transparency may require an explicit cyclotomic instance
or transport by the subsingleton Rat-algebra equality in a future provider.
Existing exponent-two/degree-at-most-two embeddings are partial results, not T17.
-/

namespace ZInQ.Targets.H

/-- Every finite abelian number-field extension of Q embeds into a cyclotomic field. -/
def T17 : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

end ZInQ.Targets.H
