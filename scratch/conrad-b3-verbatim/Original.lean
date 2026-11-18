import ZInQKernel.Contrib.OneProof.ConradBridges

/-! Verbatim copies of the starting Props and their immediate local definitions.
The one-dimensional representation and the Artin symbol are imported. -/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Bridges.Original

open Module
open scoped TensorProduct Topology Filter

set_option linter.style.longLine false

variable (p : ℕ) [Fact p.Prime]

/-- The constant weight case of the Hodge–Tate splitting in Conrad, Appendix B, pp. 32–33.
The isomorphism `ℂ_p ⊗ V ≃ ∏ ℂ_p(i)` is equivariant on pure tensors
(and hence everywhere, by additivity). This finite product is the direct sum of its lines.
The sign is Conrad's: `ℂ_p(i)` has the action `χ^i · σ`. -/
def PureHT {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (ψ : PkgI4.GQp p →* Eˣ) (i : ℤ) : Prop :=
  ∃ e : (ℂ_[p] ⊗[ℚ_[p]] (Fin 1 → E)) ≃ₗ[ℂ_[p]] (Fin (finrank ℚ_[p] E) → ℂ_[p]),
    ∀ (σ : PkgI4.GQp p) (a : ℂ_[p]) (v : Fin 1 → E) j,
      e ((PkgI4.cpAct p σ a) ⊗ₜ[ℚ_[p]]
          ((charRep ψ σ : Matrix (Fin 1) (Fin 1) E).mulVec v)) j =
        PkgI4.cycPow p σ i • PkgI4.cpAct p σ (e (a ⊗ₜ[ℚ_[p]] v) j)

/-- Restriction `G_K → G_{ℚ_p}`, using the same algebraic closure
`PadicAlgCl p` for `K` and `ℚ_p`. Its image is the fixing subgroup of `K`. -/
def restrictGalois (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* PkgI4.GQp p :=
  K.fixingSubgroup.subtype.comp K.fixingSubgroupEquiv.symm.toMonoidHom

/-- The identity coefficient line is `ℂ_p(i)` over `G_K`
(C8 at L763–764, Conrad App. B, p. 33). An isomorphism of semilinear lines
is multiplication by a nonzero scalar `c` satisfying the displayed relation. -/
def IdentityLine (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψ : PkgI4.GQp p →* Kˣ) (i : ℤ) : Prop :=
  ∃ c : ℂ_[p], c ≠ 0 ∧
    ∀ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
      let σ := restrictGalois p K g
      algebraMap K ℂ_[p] (ψ σ : K) * c = _root_.ZInQ.Contrib.G9.PkgI4.cycPow p σ i • _root_.ZInQ.Contrib.G9.PkgI4.cpAct p σ c

/-- The concrete near-1 display, Conrad App. B p. 33, local base `ℚ_p`.
The equality for `ψ ∘ r_L` is written on representatives of the arithmetic
Artin symbol in the topological abelianization. -/
def ArtinNearOne {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ψ : PkgI4.GQp p →* Eˣ) (n : ℤ) : Prop :=
  ∀ᶠ x : ℚ_[p]ˣ in 𝓝 1, ∀ σ : PkgI4.GQp p, IsArtinLift p σ x →
    ((ψ σ : Eˣ) : E) = algebraMap ℚ_[p] E (x : ℚ_[p]) ^ (-n)

/-- **CITED** (C8, sec:height, diophantine_zq.tex L760–762; Conrad, author
preprint Dec. 11, 2011, App. B pp. 32–33). The HT ⇒ local algebraicity direction
followed by the p. 33 concrete display, for local base `ℚ_p`, finite Galois
coefficients and a constant weight splitting. Only the identity embedding
of the local base contributes, giving `x ↦ x^(-n)` near 1. -/
def ConradNearOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (i : ℤ),
    Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)) →
    PureHT p ψ i → ∃ n : ℤ, ArtinNearOne p ψ n

/-- **CITED** (C8, sec:height, diophantine_zq.tex L760–764; same Conrad
preprint, App. B, p. 33, Proposition B.3). Use the identity coefficient
embedding in the printed decomposition. In the case `L = ℚ_p` the sole
exponent `n` is the weight of this line. Restrict the action to the subgroup
fixing the coefficient field. -/
def ConradIdentityWeight : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ) (n : ℤ),
    Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)) →
    ArtinNearOne p ψ n → IdentityLine p K ψ n

/-- **CITED**: the two parts of Conrad Appendix B (pp. 32–33,
including Proposition B.3) used at C8, sec:height, L760–764.
The preprint and its near-one display are used in their own normalization. -/
def ConradAppBConcrete : Prop :=
  ConradNearOne ∧ ConradIdentityWeight

example : ConradNearOne ↔ Bridges.ConradNearOne := Iff.rfl
example : ConradIdentityWeight ↔ Bridges.ConradIdentityWeight := Iff.rfl
example : ConradAppBConcrete ↔ Bridges.ConradAppBConcrete := Iff.rfl

end HDec.G0Galois.C8Conrad.Bridges.Original
