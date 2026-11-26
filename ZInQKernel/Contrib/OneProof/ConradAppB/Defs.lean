import ZInQKernel.Contrib.CloudB3W11TateTrace.TwistWholeGroup
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic

/-!
# Finite inertia for characters with a weight-zero period: statements

Let `L/ℚ_p` be finite Galois inside `ℚ̄_p` and let `χ : G_{ℚ_p} → L^×` be a continuous
character. If some nonzero `c ∈ ℂ_p` satisfies `σ c = χ(σ) c` for every `σ` fixing `L`, then
`χ` has finite image on the inertia subgroup of `G_L`. This is the rank-one case of Sen's
theorem (Serre, *Groupes algébriques associés aux modules de Hodge–Tate*, Astérisque 65
(1979), §1.4, Th. 2 and Cor. 3; Tate, *p-divisible groups* (1967), §3.3).

The proof uses three inputs, stated below as propositions:
* `UnramifiedCyclotomicSplitting`: local class field theory writes `χ = μ η`, with `μ`
  unramified and `η` trivial on the kernel of the cyclotomic character;
* `UnramifiedPeriod`: an unramified character has a nonzero period in `ℂ_p`;
* `PeriodInduction`: a period for `G_L` induces a nonzero `G_{ℚ_p}`-eigenvector in `ℂ_p ⊗ L`.
The decompletion step is the normalized-trace theorem on the cyclotomic tower over `ℚ_p`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.SenWeightZero

open ZInQ.Contrib.CloudB3W11TateTrace
open scoped TensorProduct

/-- `σ ∈ G_{ℚ_p}` lies in the inertia subgroup. -/
abbrev IsInertia (p : ℕ) [Fact p.Prime] (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Prop :=
  (show Field.absoluteGaloisGroup ℚ_[p] from σ) ∈ TauCeti.inertiaSubgroup ℚ_[p]

/-- A value of an `L`-valued character, viewed in `ℂ_p` through the inclusion of `L`. -/
abbrev cpVal (p : ℕ) [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (z : Lˣ) :
    ℂ_[p] :=
  (((z : L) : PadicAlgCl p) : ℂ_[p])

/-- Local class field theory: a continuous character splits as an unramified character times
a character that is trivial wherever the cyclotomic character is. -/
def UnramifiedCyclotomicSplitting : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ),
    Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)) →
    ∃ μ η : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ, (∀ σ, χ σ = μ σ * η σ) ∧
      Continuous (fun σ => (((μ σ : Lˣ) : L) : PadicAlgCl p)) ∧
      (∀ σ, IsInertia p σ → μ σ = 1) ∧
      (∀ σ, cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1 → η σ = 1)

/-- Hilbert 90 over the completed maximal unramified extension: an unramified continuous
character has a nonzero period in `ℂ_p` for the subgroup fixing `L`. -/
def UnramifiedPeriod : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] (μ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ),
    Continuous (fun σ => (((μ σ : Lˣ) : L) : PadicAlgCl p)) →
    (∀ σ, IsInertia p σ → μ σ = 1) →
    ∃ u : ℂ_[p], u ≠ 0 ∧ ∀ σ ∈ L.fixingSubgroup, σ • u = cpVal p (μ σ) * u

/-- Induction from `G_L` to `G_{ℚ_p}`: a nonzero period for the subgroup fixing `L` gives a
nonzero eigenvector in `ℂ_p ⊗_{ℚ_p} L` for the whole group, with the character acting on the
coefficient factor. -/
def PeriodInduction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
    (η : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ) (c : ℂ_[p]), c ≠ 0 →
    (∀ σ ∈ L.fixingSubgroup, σ • c = cpVal p (η σ) * c) →
    ∃ x : ℂ_[p] ⊗[ℚ_[p]] L, x ≠ 0 ∧ ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] L) x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((η σ : Lˣ) : L)) * x

/-- The rank-one weight-zero finite-inertia statement, for every prime. -/
def SenFiniteInertia : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Lˣ),
    Continuous (fun σ => (((χ σ : Lˣ) : L) : PadicAlgCl p)) →
    ∀ c : ℂ_[p], c ≠ 0 → (∀ σ ∈ L.fixingSubgroup, σ • c = cpVal p (χ σ) * c) →
    (Set.range fun σ : ↥(L.fixingSubgroup ⊓ TauCeti.inertiaSubgroup ℚ_[p]) => χ σ.1).Finite

end ZInQ.Contrib.SenWeightZero
