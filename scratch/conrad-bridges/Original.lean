import ZInQKernel.Contrib.OneProof.C8ConradB

/-! Exact copies of the old Conrad Props and the local definitions they
unfold. The underlying field, Galois, reciprocity and representation
objects are imported from their defining modules. -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad.Original
open Module

section
variable (p : ℕ) [Fact p.Prime]

/-- **Locally algebraic of exponent `n`** (Conrad, Def. B.1, for the base field `ℚ_p`: the only algebraic characters
of `Res_{ℚ_p/ℚ_p} 𝔾_m = 𝔾_m` are `x ↦ x^n`): `ψ ∘ Art_{ℚ_p}` agrees with `x ↦ x^n` on an open subgroup of `ℤ_p^×`,
here `1 + p^k ℤ_p`. -/
def IsLocallyAlgebraic {E : Type*} [Field E] [Algebra ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) : Prop :=
  ∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
    IsArtinLift p σ (unitsQp p u) → ((ψ σ : Eˣ) : E) = (algebraMap ℚ_[p] E ((u : ℤ_[p]) : ℚ_[p])) ^ n

/-- **Locally algebraic of exponent `n` in Conrad's normalization** (Conrad, *Lifting global representations with local
properties*, author preprint Dec. 11, 2011, App. B, p. 33, for the base field `L = ℚ_p`, whose only embedding is the
identity): near `1`, `ψ ∘ r_{ℚ_p}` agrees with `x ↦ x^{-n}`, where `r_{ℚ_p}` is the arithmetically normalized local
Artin map (p. 32; here Tau Ceti's, through `IsArtinLift`). "Near `1`" is read on the open subgroups `1 + p^k ℤ_p`,
which form a basis of neighbourhoods of `1` in `ℚ_p^×`. -/
def IsLocallyAlgebraicConrad {E : Type*} [Field E] [Algebra ℚ_[p] E] (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) : Prop :=
  ∃ k : ℕ, ∀ u : ℤ_[p]ˣ, PadicInt.toZModPow k (u : ℤ_[p]) = 1 → ∀ σ : PkgI4.GQp p,
    IsArtinLift p σ (unitsQp p u) → ((ψ σ : Eˣ) : E) = (algebraMap ℚ_[p] E ((u : ℤ_[p]) : ℚ_[p])) ^ (-n)

/-- **Multiplicity of the Hodge–Tate weight `w` in Conrad's convention** (`χ_cyc` has weight `+1`; Conrad App. B p. 33:
`ℂ_L ⊗ V = ⊕ V_σ` with `V_σ ≅ ℂ_L(w_σ)`, and `{w_σ}` is the set of Hodge–Tate weights) of the underlying
`ℚ_p`-representation of `ρ`: `dim_{ℚ_p} H_w(ρ)`, where `H_w(ρ) = (ℂ_p(w) ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}` is the project's
`htSpace` (equivariant `ℚ_p`-linear maps `V → ℂ_p(w)`). Check: for `V = ℚ_p(1)`, `H_w ≠ 0` iff `w = 1` (`htMult`'s
docstring, by Tate's theorem), i.e. `χ_cyc` has Conrad weight `+1`. Dictionary: if `ℂ_p ⊗_{ℚ_p} V ≅ ⊕_σ ℂ_p(w_σ)` then
`H_w ≅ ⊕_σ ℂ_p(w − w_σ)^{G_{ℚ_p}}`, of `ℚ_p`-dimension `#{σ : w_σ = w}` (Tate's two theorems over `ℚ_p`, both proved in
the tree: `CloudB3W11.tateTwistInvariants_proof`, `CloudB3W11.axSenTate_proof`). -/
def conradHTMult {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {m : ℕ}
    (ρ : PkgI4.GQp p →* GL (Fin m) E) (w : ℤ) : ℕ :=
  finrank ℚ_[p] (PkgI4.htSpace p ρ w)

end

/-- **LEAF candidate (printed-form instance; unrefereed preprint).** B. Conrad, *Lifting global representations with
local properties*, author preprint, December 11, 2011, Appendix B, pp. 32-33 (the manuscript's citation
`conrad-local-characters`, diophantine_zq.tex L761, L11046-11049): the paragraph after Definition B.1, "a continuous
character with values in a finite extension of `ℚ_p` is locally algebraic exactly when its underlying
`ℚ_p`-representation is Hodge–Tate" (as reported by the theorem-application audit,
`docs/theorem-application-audit/evidence/parallel-galois-height-report.md` L102; not read on this host), in the case
of base field `L = ℚ_p`, direction Hodge–Tate ⇒ locally algebraic. Coefficient field: a finite extension `E/ℚ_p` inside
`ℚ̄_p`. Hodge–Tate is the project's `PkgI4.HasHTWeights` with a single weight `w` (that is, `dim_{ℚ_p} H_{−w} ≥ [E:ℚ_p]`,
which forces the underlying `ℚ_p`-representation to be Hodge–Tate by the Serre–Tate inequality `Σᵢ dim Hᵢ ≤ [E:ℚ_p]`:
a dictionary step, so this Lean form is a consequence of the printed statement, not verbatim). -/
def ConradAppBQp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ), Continuous (fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) →
    (∃ w : ℤ, PkgI4.HasHTWeights p (charRep ψ) {w}) → ∃ n : ℤ, IsLocallyAlgebraic p ψ n

/-- **LEAF candidate, CITED (diophantine_zq.tex L760-762; Conrad, *Lifting global representations with local
properties*, author preprint, December 11, 2011, App. B, p. 33, Prop. B.3 (proof pp. 33-34); bibitem
`conrad-local-characters`, L11046-11049; flag: AI page read 11-17, unrefereed preprint, the manuscript's own
citation).** Prop. B.3 says that for a locally algebraic `ψ` the Hodge–Tate weight `w_σ` equals `n_i`, for the factor
`i` through which `σ ⊗ 1` factors. Specialised to the base field `L = ℚ_p` (one embedding, one factor, one exponent
`n`) and a coefficient field `E/ℚ_p` finite inside `ℚ̄_p`, in Conrad's conventions (arithmetic Artin map; `χ_cyc` of
weight `+1`): if `ψ : G_{ℚ_p} → E^×` is continuous and `ψ ∘ r_{ℚ_p}` is `x ↦ x^{-n}` near `1`, then every one of the
`[E : ℚ_p]` Hodge–Tate weights `w_σ` of the underlying `ℚ_p`-representation is `n`, i.e. `conradHTMult n = [E : ℚ_p]`.
The Lean conclusion is a consequence of the printed one: `ℂ_p ⊗_{ℚ_p} V ≅ ℂ_p(n)^{[E:ℚ_p]}` gives
`H_n ≅ (ℂ_p^{G_{ℚ_p}})^{[E:ℚ_p]} = ℚ_p^{[E:ℚ_p]}` (Ax–Sen–Tate over `ℚ_p`, proved in the tree as
`CloudB3W11.axSenTate_proof`). -/
def ConradPropB3Qp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ), Continuous (fun σ => (((ψ σ : Eˣ) : E) : PadicAlgCl p)) →
    IsLocallyAlgebraicConrad p ψ n → conradHTMult p (charRep ψ) n = finrank ℚ_[p] E

/-- **LEAF candidate, CITED: Conrad's App. B for the base field `ℚ_p`** (diophantine_zq.tex L760-762, "[Appendix B,
pp. 32-33]{conrad-local-characters}"): p. 32 (`ConradAppBQp`: a Hodge–Tate character is locally algebraic) and p. 33,
Prop. B.3 (`ConradPropB3Qp`: its Hodge–Tate weight is the exponent). Flags: unrefereed author preprint (the
manuscript's own citation); p. 32's Hodge–Tate ⇒ locally algebraic paragraph as reported by the theorem-application
audit, Prop. B.3 by the AI page read of 11-17. -/
def ConradAppB : Prop :=
  ConradAppBQp ∧ ConradPropB3Qp

example : ConradAppBQp ↔ _root_.HDec.G0Galois.C8Conrad.ConradAppBQp := Iff.rfl
example : ConradPropB3Qp ↔ _root_.HDec.G0Galois.C8Conrad.ConradPropB3Qp := Iff.rfl
example : ConradAppB ↔ _root_.HDec.G0Galois.C8Conrad.ConradAppB := Iff.rfl

end HDec.G0Galois.C8Conrad.Original
