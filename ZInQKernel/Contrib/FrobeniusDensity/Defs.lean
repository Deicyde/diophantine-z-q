import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The minimal valuation-level statement of T18

This contribution deliberately does not import the unregistered H targets.
The declaration bodies below are faithful copies of the relevant definitions
and target statement in the draft statement extraction at public PR 41, revision
`2757349fbd8ca613340b679bbd149f78c2baba6b`. They are local to this contribution,
not registrations or proof providers for that draft.

Arithmetic Frobenius means the forward residue map `x ↦ x ^ p`, and the
approximation convention is `τ⁻¹ * σ ∈ U`. No Frobenius existence or density
hypothesis is hidden in a typeclass.
-/

namespace ZInQ.Contrib.FrobeniusDensity

/-- The algebraic closure of the rational numbers. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- The absolute Galois group with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- The prime `p` belongs to the maximal ideal of the valuation subring. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  (p : Qbar) ∈ v.nonunits

/-- Arithmetic, not geometric, Frobenius at the actual valuation subring. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- The exact closed valuation-level proposition proposed as H target T18. -/
def T18 : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

end ZInQ.Contrib.FrobeniusDensity
