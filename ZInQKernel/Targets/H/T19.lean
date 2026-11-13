import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# First H batch: T19, Brauer–Nesbitt in characteristic zero

Proposed closed target, reserved provider `ZInQ.Contrib.H.T19_holds`.
This registration draft is not mathematical or protected Astra acceptance.

The statement body preserves PR #41's `ZInQ.Targets.H.T19` at
`2757349fbd8ca613340b679bbd149f78c2baba6b`, from `HSyn.BrauerNesbitt`
in the frozen reference `Leaves.lean` at `48b5f075e5509678c84685f0d1ec53febd10b1e5`.
Reference file SHA-256: `99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`.

Reference locators: Curtis–Reiner section 30; Lang Algebra XVII 3.8 (subject to
source review). G is arbitrary, not assumed finite; E need not be algebraically
closed. Each representation's semisimplicity is stated as the existence of an
invariant complementary subspace for every invariant subspace. Equal traces on
all group elements must yield one invertible matrix conjugating all elements,
including dimension zero. A finite-group or absolutely semisimple special case
is not a proof of this target. All objects are Mathlib objects, not custom HSyn.
-/

open scoped MatrixGroups

namespace ZInQ.Targets.H

/-- Exact trace/complement form of Brauer–Nesbitt for arbitrary groups in characteristic zero. -/
def T19 : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

end ZInQ.Targets.H
