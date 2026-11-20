import ZInQKernel.Contrib.OneProof.ConradB3Verbatim
import ZInQKernel.Contrib.TauCeti.RingTheory.Norm.Units

/-!
# Serre's Appendix to Chapter III: characters attached to Hodge–Tate decompositions

Step C8 (diophantine_zq.tex, sec:height, L760–764) cites Conrad's Appendix B, pp. 32–34, which is
an unpublished preprint. Its proof of the p. 32 equivalence and of Proposition B.3 rests on the
published Appendix to Chapter III of

* J.-P. Serre, *Abelian `l`-adic representations and elliptic curves*, McGill University
  Lecture Notes written with the collaboration of W. Kuyk and J. Labute, Addison-Wesley,
  Advanced Book Classics, 1989 (originally W. A. Benjamin, 1968), ISBN 0-201-09384-7.

All page numbers below are those of that edition, checked against the scan.

* III-34, A2, Definition and Remark 1. A continuous character `φ : G → K^*` of
  `G = Gal(K̄/K)` is *admissible*, `φ ∼ 1`, if some `x ∈ C`, `x ≠ 0`, satisfies `s(x) = φ(s) x`
  for all `s ∈ G`. Here `C` is the completion of `K̄`. One writes `φ ∼ φ'` if `φ⁻¹ φ' ∼ 1`.
* III-44, A5, Theorem 2, condition (ii): `σ ∘ ρ ∼ χ^{n_σ}` for all `σ ∈ Γ_E`. Here
  `ρ : G → U_E` is continuous, `E` is a finite extension of `ℚ_p` all of whose
  `ℚ_p`-conjugates lie in the ground field `K`, `Γ_E` is the set of `ℚ_p`-embeddings `E → K`,
  and `χ` is the cyclotomic character (Chapter I, 1.2).
* III-47/48, A6. `K` is finite over `ℚ_p`. `r_σ = σ⁻¹ ∘ N_{K/σE} : T → T_E`, with
  `r_σ(u⁻¹) = σ⁻¹ ∘ χ_{σE}(u)` on `U_K` (Proposition 5 (a)).
* III-49/50, A6, Proposition 6. With `r = ∏ r_σ^{n_σ}`, the equivalent conditions (i), (ii),
  (iii) of Theorem 2 are equivalent to (iv): there is an open subgroup `U'` of the inertia
  subgroup `U_K` of `G^{ab}` such that `r(u) ρ(u) = 1` for `u ∈ U'`. The inertia subgroup is
  identified with `U_K` by local class field theory (III-47, the first paragraph of A6), with
  Serre's normalization `i` of III-2 (Cassels–Fröhlich, Chapter VI, §2). Under it, the
  cyclotomic character is `u ↦ u⁻¹` on `U_{ℚ_p}` (III-2, Example 1, `ν = -1`). This is the
  arithmetic normalization, which is Tau Ceti's (`IsArtinLift`).

## The case used here

We take Serre's ground field `K` and coefficient field `E` both equal to a finite Galois
extension `K` of `ℚ_p` inside `ℚ̄_p`. Then `Γ_E = Gal(K/ℚ_p)`, `σE = K`, `N_{K/σE} = id`, and
`r_σ(u) = σ⁻¹(u)`. The character `ρ` is the restriction to `G_K` (the fixing subgroup of `K`,
`restrictGalois`) of a continuous `ψ : G_{ℚ_p} → K^×`; continuity and compactness put its values
in `U_K`.

## GLUE: reading (iv) through norm functoriality

Serre's `ρ(u)` in (iv) means `ρ(i_K(u))` for the reciprocity map `i_K` of the ground field `K`.
Since `ρ = ψ|_{G_K}` and `ψ` factors through `G_{ℚ_p}^{ab}`, `ρ(i_K(u)) = ψ(i_{ℚ_p}(N_{K/ℚ_p} u))`.
This is the norm functoriality of local class field theory: Serre III-5, the commutative
diagram `K'^* → Gal(K̄/K')^{ab}`, `K^* → Gal(K̄/K)^{ab}` with the norm on the left. Tau Ceti
proves it as `TauCeti.ClassFieldTheory.artinMap_norm`, but only for types carrying the
nonarchimedean local field structure (`IsNonarchimedeanLocalField`). The intermediate field `K`
of `ℚ̄_p` has no such instances in the tree. So `SerreA6Print` states (iv) directly with
`artinMap ℚ_[p]` applied to `TauCeti.Algebra.normUnits ℚ_[p] u`.
**This rewriting step is GLUE.** The
rest of the statement is Serre's Theorem 2 (ii) ⇔ Proposition 6 (iv), verbatim in the case
above.

The sign conventions agree with Conrad's (`PureHT`, `ℂ_p(w)` with action `χ^w σ`). By Serre's
Lemma 1 (c) (III-43), the `σ`-line `W_σ` of `C ⊗_{ℚ_p} V` is `C(σ ∘ ρ)`, and (ii) says
`C(σ ∘ ρ) ≅ C(χ^{n_σ})`. With `n_σ = n` for all `σ`, (iv) reads
`ψ(i_{ℚ_p}(N u)) = N(u)^{-n}`, Conrad's display (B.1) at `L = ℚ_p`.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.SerreAppB

open HDec.G0Galois.C8Conrad.Bridges
open Module
open scoped TensorProduct Topology Filter

variable (p : ℕ) [Fact p.Prime]

/-- Serre III-34 (A2, Definition and Remark 1), applied as in III-44 (A5, Theorem 2 (ii)):
`σ ∘ ρ ∼ χ^n` on `G_K`, where `ρ = ψ|_{G_K}`. Admissibility of `(σ ∘ ρ)⁻¹ χ^n` means: some
nonzero `x ∈ ℂ_p` satisfies `g(x) = (σ ρ(g))⁻¹ χ(g)^n x` for all `g ∈ G_K`. Kind: definition
(transcription). -/
def SerreTwistAdmissible (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ψ : PkgI4.GQp p →* Kˣ) (σ : K ≃ₐ[ℚ_[p]] K) (n : ℤ) : Prop :=
  ∃ x : ℂ_[p], x ≠ 0 ∧ ∀ g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p,
    _root_.ZInQ.Contrib.G9.PkgI4.cpAct p (restrictGalois p K g) x =
      (algebraMap K ℂ_[p] (σ ((ψ (restrictGalois p K g) : Kˣ) : K)))⁻¹ *
        algebraMap ℚ_[p] ℂ_[p] (_root_.ZInQ.Contrib.G9.PkgI4.cycPow p (restrictGalois p K g) n) * x

/-- Serre III-50 (A6, Proposition 6, condition (iv)) in the case `E = K` Galois. There is an open
subgroup `U'` of `U_K` (an open subgroup of `Kˣ` made of units) such that
`ρ(u) · ∏_σ σ⁻¹(u)^{n_σ} = 1` for `u ∈ U'`. Here `ρ(u)` is read as
`ψ(i_{ℚ_p}(N_{K/ℚ_p} u))`, the GLUE step of the module docstring (Serre III-5; Tau Ceti
`artinMap_norm`). Kind: definition (transcription, with the GLUE reading). -/
def SerreA6NormForm (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ) : Prop :=
  ∃ U : Subgroup Kˣ, IsOpen (U : Set Kˣ) ∧
    ∀ u ∈ U, ‖(((u : Kˣ) : K) : PadicAlgCl p)‖ = 1 ∧
      ((conradAbelianChar p ψ hc
          (TauCeti.ClassFieldTheory.artinMap ℚ_[p] (TauCeti.Algebra.normUnits ℚ_[p] u)) : Kˣ) : K) *
        ∏ σ : K ≃ₐ[ℚ_[p]] K, σ.symm ((u : Kˣ) : K) ^ n σ = 1

/-- **PRINT + GLUE** (Serre, *Abelian `l`-adic representations*, 1989 ed., Appendix to
Chapter III: A5, Theorem 2 (ii), p. III-44 ⇔ A6, Proposition 6 (iv), pp. III-49–50, with the
definitions of III-34 and III-47/48). The ground field and coefficient field are a finite Galois
`K/ℚ_p` inside `ℚ̄_p`, and `ρ = ψ|_{G_K}`. The equivalence is printed. Reading `ρ(u)` as
`ψ(i_{ℚ_p}(N_{K/ℚ_p} u))` in (iv) is GLUE: norm functoriality of local class field theory
(Serre III-5; proved by Tau Ceti as `artinMap_norm` for local-field types, not instantiated at
`K`). Kind: named input. -/
def SerreA6Print : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (ψ : PkgI4.GQp p →* Kˣ)
    (hc : Continuous (fun σ => (((ψ σ : Kˣ) : K) : PadicAlgCl p)))
    (n : (K ≃ₐ[ℚ_[p]] K) → ℤ),
    (∀ σ : K ≃ₐ[ℚ_[p]] K, SerreTwistAdmissible p K ψ σ (n σ)) ↔ SerreA6NormForm p K ψ hc n

end HDec.G0Galois.C8Conrad.SerreAppB
