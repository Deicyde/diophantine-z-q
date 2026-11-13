import ZInQKernel.Contrib.FrobeniusDensity.ClosedProof

/-!
# Exact frozen-reference full-type check

The body of `frozenT18Reference` below is copied verbatim from the frozen,
unregistered draft `Targets/H/T18.lean` at public revision
2757349fbd8ca613340b679bbd149f78c2baba6b, with only the definition's name
and surrounding namespace changed. It uses the already checked faithful
minimal local definitions; no unregistered module is imported.
-/

namespace ZInQ.Contrib.FrobeniusDensity

/-- The frozen draft T18 body, independently retained for the scoped raw type audit. -/
def frozenT18Reference : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

example : frozenT18Reference = T18 := rfl
example : frozenT18Reference := t18_holds

end ZInQ.Contrib.FrobeniusDensity
