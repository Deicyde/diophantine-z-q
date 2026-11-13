
/-! (fast-environment copies of part_weight.lean's `IsConj`, `HTConj`; not used in Weight.lean) -/
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)

/-- `r` and `ρ'` are conjugate by a fixed matrix: `r(σ) = P ρ'(σ) P⁻¹`. -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **Hodge–Tate weights are invariant under conjugation (GLUE, about the definition
`PkgI4.LocalHasHTWeights`; STANDARD).** Enlarge the finite coefficient field `E` to contain the
entries of `P` and `P⁻¹` and use that `htMult` does not change under a finite extension of `E`
(`(ℂ_p(i) ⊗ V)^G` commutes with `E'/E` base change) nor under an `E'`-linear isomorphism. -/
def HTConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (r ρ' : GaloisRep ℓ n) (S : Multiset ℤ),
    IsConj r ρ' → r.HasHTWeightsAtSelf ℓ S → ρ'.HasHTWeightsAtSelf ℓ S

end G0Galois
