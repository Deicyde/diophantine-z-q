
/-! ## g0-mod-galois: glue steps G8-G12 of the H decomposition (task g0-mod-galois, 2026-11-13)

`ModularConstituent` (scratch/g0-split) bundles G2, G4, G7-G16. This section takes the range
G8-G12 (h-decomposition §3; N5 L719-768; h-trust C1-C8):

* G8  `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, the Tate action on `G_{L'}`, `r_ℓ|G_{L'}` absolutely irreducible;
* G9  `r_ℓ` de Rham at `ℓ` with Hodge–Tate weights `{0, −1}`;
* G10 `r_ℓ` odd;
* G11 `r_ℓ` unramified outside `T ∪ {ℓ}`;
* G12 Pan at `ℓ = 5`: `r₅` is attached, up to a twist `ψ` of **finite image**, to a normalized
  eigenform of **weight 2**.

Inputs are the outputs of the earlier glue steps, as `def … : Prop`: `G2Out` (the field is
unramified outside `T`), `G3Out` (the Tate action is unramified outside `T ∪ {ℓ}`), `G7Out` (the
scalar-descent data `T_σ = μ_σ ∘ σ`, `a`, `β`, and the matrix units of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`).
The coefficient field is `ℚ̄_ℓ = PadicAlgCl ℓ` throughout (Pan's coefficients). The remaining
unproved glue is named: `G8Matrix` (linear algebra), `G9Glue`, `G10Glue`, `G12Weight`, `G12Det`.
Proved here: G8 from `G7Out`, C2 and `G8Matrix`; G11 from `G2Out`, `G3Out` and G8's output, with
no further glue; G12 from Pan∘Berger (R11+R12), `weight_match`, `twist_finite` and the two named
G12 pieces. -/

section G0GaloisSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Objects -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmbRing` as a `ℚ`-algebra map (the `i` of g0-mod-newform's `ModData`). -/
def qEmb (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
  (qEmbRing K).toRatAlgHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- `resQ K τ` is the only `σ ∈ G_ℚ` with `qEmb K ∘ σ = τ ∘ qEmb K`. -/
lemma eq_resQ (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (σ : PkgI4.GQ) (h : ∀ x, qEmb K (σ x) = τ (qEmb K x)) : σ = resQ K τ := by
  apply AlgEquiv.ext; intro x
  exact (qEmbRing K).injective ((h x).trans (resQ_spec K τ x).symm)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- The restriction of a representation to an invariant subspace. -/
def restrictRep {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (W : Submodule k V) (h : ∀ g, ∀ w ∈ W, ρ g w ∈ W) :
    Representation k G W where
  toFun g := (ρ g).restrict (h g)
  map_one' := by ext w; simp
  map_mul' g g' := by ext w; simp

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-! ### Outputs of the earlier glue steps (inputs of this range) -/

/-- **Output of G2 (Lemma PR(i)), the part used here.** The field `K` (= `L'`, which contains
the fibre field and the Hom field, both unramified outside `T`, and the kernel field of `β`,
unramified outside `T` by B3(v)) is unramified at every prime `p ∉ T`: every inertia element
of `G_ℚ` at a place above `p` lies in (the image of) `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- **Output of G3 (Lemma PR(ii)) with R7a (Néron–Ogg–Shafarevich), the part used here.** `A`
has good reduction at the places above `p ∉ T`, so for `p ≠ ℓ` the inertia elements of `G_K`
at those places act trivially on `V_ℓ(A)` (the instantiation of
`PkgI2.inertiaTrivial_of_goodReduction` on the actual `A`, glue G3/G11). -/
def G3Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ' : Field.absoluteGaloisGroup K,
      (∃ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = resQ K σ') →
      tate A ℓ σ' = 1

/-- **Output of G7 (scalar descent, N5 L632-716) at the coefficient prime `ℓ`**, together with
the outputs of G4-G6 that G8 uses. `A` is the model over `K = L'` (an abelian surface with
`End_K(A)` of rank 4, the maximal order case of `End⁰ = B`: A9's output). The data are:
operators `Tm σ = μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` (without `a_σ`: `GlueDescent.rho` multiplies by
`β_σ⁻¹ a_σ`, giving N5's `ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ`) with the cocycle `c` (`Tm g Tm h = c(g,h) Tm(gh)`),
the scalars `a` and the cochain `β` with `a_g a_h c(g,h) = ε(g,h) a_{gh}` and
`β_g β_h = ε(g,h) β_{gh}` (`∂β = ε`, B2-B3), all trivial on `G_{L'}` where `Tm` is the Tate
action (`L'` contains the kernel field of `β|G_L`; it is taken finite Galois over `ℚ`, as
g0-mod-field's `G7Data` supplies, which `G10Glue` needs); a system of `2 × 2` matrix units (the image of
`B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`) commuting with every `Tm σ` (`μ_σ` is `B`-linear); and continuity of
`σ ↦ β_σ⁻¹ a_σ Tm σ` (glue-rho-cont proved continuity on `G_K`; finite index gives the rest). -/
def G7Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

/-- **Output of G5-G6 (QM dichotomy and NoCM), the part used by G10:** `End_K(A)` is a division
ring (`PkgI3.EndDivision`: every nonzero endomorphism is an isogeny) and is not commutative (so
`End⁰_K(A) = B`, not a field). -/
def G6Out {K : Type} [Field K] (A : PkgI3.AbVar K) : Prop :=
  PkgI3.EndDivision A ∧ ∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x

/-! ### Outputs of this range -/

/-- **Output of G8.** `r : G_ℚ → GL₂(ℚ̄_ℓ)` (continuous) and `e : ℚ̄_ℓ ⊗ V_ℓ(A) ≅ ℚ̄_ℓ² × ℚ̄_ℓ²`
with: (i) `e` intertwines the descended representation `ρ` (an operator family on
`ℚ̄_ℓ ⊗ V_ℓ(A)`, in the theorem `GlueDescent.rho Tm a β`) with `r ⊕ r` on all of `G_ℚ`;
(ii) `ρ` is the Tate action on `G_{L'}`; (iii) `r|G_{L'}` is absolutely irreducible, in
Burnside's form (the matrices `r(σ)`, `σ ∈ G_{L'}`, generate `M₂(ℚ̄_ℓ)`). -/
def G8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2) : Prop :=
  (∀ σ, ρ (resQ K σ) = tate A ℓ σ) ∧
  ∃ e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ),
    Intertwines ρ r.mat e ∧
    Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤

/-- **Output of G9** (N5's appendix lemma `lem:de-rham-descent`, L10939-11000):
`r|G_{ℚ_ℓ}` is de Rham, with Hodge–Tate weights `{0, −1}` (Tate convention, cyclotomic weight
`−1`; pkg-I4's `LocalIsDeRham`, `HasHTWeightsAtSelf`). -/
def G9Out {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop :=
  PkgI4.LocalIsDeRham ℓ 2 (r.restrictLocal ℓ) ∧ r.HasHTWeightsAtSelf ℓ {0, -1}

/-- **Output of G10:** `r` is odd (`det r(c) = −1` for every complex conjugation `c`). -/
def G10Out {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop := r.IsOdd

/-- **Output of G11:** `r` is unramified at every prime outside `T ∪ {ℓ}`. -/
def G11Out {ℓ : ℕ} [Fact ℓ.Prime] (T : Finset ℕ) (r : GaloisRep ℓ 2) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ → r.UnramifiedAt p

instance fact_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Output of G12** (at `ℓ = 5`; N5 L755-768, h-trust C7-C8): there are a level `N ≥ 1`, a
normalized eigenform `g` of **weight 2** on `Γ₁(N)` with nebentypus `χ`, a continuous character
`ψ : G_ℚ → ℚ̄₅^×` of **finite image**, embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄₅` and a finite set
`S` of primes, such that `r` is attached to `g` up to the twist `ψ` outside `S`:
`tr r(Frob_q) = ψ(Frob_q) ιL(a_q(g))` for `q ∉ S` (arithmetic Frobenius). -/
def G12Out (r : GaloisRep 5 2) : Prop :=
  ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    0 < N ∧ PkgI4.IsNormalizedEigenform g χ ∧ (Set.range ψ.toHom).Finite ∧
    r.AttachedUpToTwist ψ ιC ιL g S

/-! ### The remaining glue, named -/

/-- **G8, linear-algebra remainder (GLUE, unproved; STANDARD).** Let `ρ` be a representation of
`G_ℚ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` commuting with a system of `2 × 2` matrix units `u`,
weakly continuous, such that `r_W := ρ|_{W}` on `W = e₀₀(ℚ̄_ℓ ⊗ V_ℓ(A))` is absolutely irreducible
on `G_K` (C2's conclusion: irreducible after every field extension), and
`dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` (proved in `g8` from T26 and `dim A = 2`). Then a basis of `W`
(`dim W = 2`, `GlueDescent.MatrixUnits2.finrank_W`) turns `r_W` into a
continuous `r : G_ℚ → GL₂(ℚ̄_ℓ)`, `splitEquiv` composed with that basis intertwines `ρ` with
`r ⊕ r`, and Burnside's theorem over the algebraically closed `ℚ̄_ℓ` (from Mathlib's
`jacobson_density`) gives that `r(G_K)` spans `M₂(ℚ̄_ℓ)`. No arithmetic input. -/
def G8Matrix : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : Representation (PadicAlgCl ℓ) PkgI4.GQ (Vb A ℓ))
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ))
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)),
    Module.finrank (PadicAlgCl ℓ) (Vb A ℓ) = 4 →
    (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ), Continuous fun g => f (ρ g v)) →
    (∀ (F : Type) [Field F] [Algebra (PadicAlgCl ℓ) F],
      (GlueI3.repBaseChange F
        ((restrictRep ρ u.W (fun g _ hw => u.mapsTo_W ρ hc g hw)).comp (resQ K))).IsIrreducible) →
    ∃ (r : GaloisRep ℓ 2) (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
      Intertwines (fun g => ρ g) r.mat e ∧
      Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤

/-- **G9, N5's appendix lemma (GLUE, unproved; two model reviews, h-trust C3).** From R10
(`PkgI4.DeRhamComparison`: `V_ℓ` of an abelian variety over a finite extension `F/ℚ_ℓ` is de Rham
with weights `0, −1` each of multiplicity `dim`) and T23 (Fontaine's closure under
subquotients and direct sums): if `r : G_ℚ → GL₂(ℚ̄_ℓ)` and `ℚ̄_ℓ ⊗ V_ℓ(A) ≅ r|G_K ⊕ r|G_K` for an
abelian surface `A` over a number field `K`, then `r|G_{ℚ_ℓ}` is de Rham with weights `{0, −1}`.
Proof plan (h-trust C3, Galois choice): base change `A` to a completion `F` of a Galois closure at
a place above `ℓ`; `r|G_F` is a summand of `V_ℓ(A_F) ⊗ ℚ̄_ℓ`, hence de Rham with weights
`{0, −1}` (each weight of `V_ℓ(A_F)` has multiplicity 2 = twice its multiplicity in `r`); descend
from `F` to `ℚ_ℓ` by Hilbert 90 (`B_dR^{G_F} = F`). Needs: base change of `PkgI3.AbVar` to
local fields, the comparison of `PkgI3.AbVar` with pkg-I4's copy `PkgI4.I3.AbVar`, and a
finite-coefficient-field reduction (a continuous `G_{ℚ_ℓ} → GL₂(ℚ̄_ℓ)` has values in a finite
extension, Baire). True by the published inputs (R10, T23) and STANDARD descent. -/
def G9Glue : Prop :=
  PkgI4.DeRhamComparison → (∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p) →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r

/-- **G10, oddness (GLUE, unproved; h-trust C5, model reviews).** From T11 (Riemann, GAGA) and T12
(Artin comparison) with R9b (Faltings): if `K` is Galois over `ℚ`, `A/K` an abelian surface with
`End_K(A)` of rank 4, a division ring (`PkgI3.EndDivision`) and noncommutative (so `End⁰_K(A)`
is a quaternion algebra over `ℚ`), and `r : G_ℚ → GL₂(ℚ̄_ℓ)` with
`ℚ̄_ℓ ⊗ V_ℓ(A) ≅ r|G_K ⊕ r|G_K`, then `r` is odd. Argument (model review, SPECULATIVE until
written; each step STANDARD): `r(c)² = 1`; if `r(c) = ±1` then `ρ(c)` is scalar and, `G_K` being
normal, `c` induces a `G_K`-equivariant map `V_ℓ(cA) → V_ℓ(A)`, which by Faltings (R9b) lies in
`Hom(cA, A) ⊗ ℚ_ℓ`; by Artin comparison (T12) it is the antiholomorphic `F_∞`, a rational map,
contradicting holomorphy of homomorphisms (T11). So `r(c)` is not scalar, and `det r(c) = −1`.
(This is N5 L742-751's Betti argument; the rank/division/noncommutativity hypotheses are not
needed by it but are kept, being true for Glazer's `A`.) -/
def G10Glue : Prop :=
  HSyn.T11_RiemannGAGA → HSyn.T12_ArtinComparison → PkgI3.FaltingsTate →
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Module.finrank ℤ (PkgI3.AbVar.End A) = 4 → PkgI3.EndDivision A →
    (∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x) →
    Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G10Out r

/-- **G12, the weight comparison (GLUE, unproved; h-trust C8 "Content", rv-h-c8).** From R14
(eigenform representations), R13 (their Hodge–Tate weights `{0, 1 − k}` for `k ≥ 2`, every
level), R15 (Deligne–Serre for `k = 1`), T18 (Chebotarev) and T19 (Brauer–Nesbitt): if an
irreducible `r : G_ℚ → GL₂(ℚ̄₅)` with weights `{0, −1}` at 5 is attached to a normalized eigenform
`g` of weight `k ≥ 1` up to a continuous twist `ψ` outside a finite set, then the weights of `r`
are `{n, n + 1 − k}` for an integer `n`. Argument: `r ≅ ρ_g ⊗ ψ` (traces agree on a dense set,
both semisimple); the Sen weights of `ρ_g ⊗ ψ` are `{0, 1−k} + s` (`s` the Sen weight of `ψ`,
a priori not an integer); equality with `{0, −1}` forces `s = 0`, `k = 2` for `k ≥ 2`
(model review: `ψ` itself need not be Hodge–Tate a priori, so the argument goes through Sen
weights); for `k = 1`, `ρ_g` has finite image, hence weights `{0, 0}`, so
`r` would have equal weights, contradicting `{0, −1}` (so the hypotheses are inconsistent). -/
def G12Weight : Prop :=
  HSyn.EigenformRepExists → PkgI4.EigenformHT → HSyn.DeligneSerreConseq → HSyn.FrobeniusDense →
  HSyn.BrauerNesbitt →
  ∀ (r : GaloisRep 5 2) (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (S : Finset ℕ),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ → r.IsIrreducible →
    r.HasHTWeightsAtSelf 5 {0, -1} → r.AttachedUpToTwist ψ ιC ιL g S →
    ∃ n : ℤ, ({n, n + 1 - k} : Multiset ℤ) = {0, -1}

/-- **G12, the determinant identities (GLUE, unproved; h-trust C8 items 1-3, V16 L660-667).**
For `r` as in G8's output on the model `A/K` and `r ≅ ρ_g ⊗ ψ` with `g` of weight 2 and
nebentypus `χ`: there are characters `det r`, `ε` (the nebentypus as a Galois character, of
finite image), `χ_cyc` (the 5-adic cyclotomic character) of `G_ℚ` and a finite-index subgroup
`H` (`G_K`: a polarization exists over `K`) with `det r = ε · χ_cyc · ψ²`
(`det ρ_g = ε χ_cyc` at `k = 2`, the determinant clause of R14 as published) and
`(det r)² = χ_cyc²` on `H` (T9: `det V₅(A) = χ_cyc²` on `G_F`, with `V₅(A) ≅ r ⊕ r`). The
group theory that turns this into the finiteness of `ψ` is `GlueAssembly.twist_finite`
(proved). -/
def G12Det : Prop :=
  HSyn.EigenformRepExists → LeafPush.T09_WeilPairing.{0} →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (r : GaloisRep 5 2)
    (e : Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    A.dim = 2 → Intertwines (tate A 5) (fun σ => r.mat (resQ K σ)) e →
    0 < N → PkgI4.IsNormalizedEigenform g χ → r.AttachedUpToTwist ψ ιC ιL g S →
    ∃ (H : Subgroup PkgI4.GQ) (_ : H.FiniteIndex) (dr εg χc : PkgI4.GQ →* (PadicAlgCl 5)ˣ),
      (∀ x, dr x = εg x * χc x * ψ.toHom x ^ 2) ∧ (∀ h ∈ H, dr h ^ 2 = χc h ^ 2) ∧
      (Set.range εg).Finite

/-! ### Proofs -/

/-- `ρ` restricted along `resQ` gives the Tate-action form of the intertwining. -/
theorem intertwines_res {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ}
    [Fact ℓ.Prime] {ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)} {r : GaloisRep ℓ 2}
    {e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (hres : ∀ σ, ρ (resQ K σ) = tate A ℓ σ) (h : Intertwines ρ r.mat e) :
    Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e := by
  intro σ v
  have := h (resQ K σ) v
  rwa [hres σ] at this

/-- **G8 (proved from `G7Out`, the leaves R9a, R9b, T6, T26, `SemisimpleBaseChange` through C2,
and the linear-algebra remainder `G8Matrix`).** The descended operators `ρ = β⁻¹ a Tm` form a
representation of `G_ℚ` (`GlueDescent.rho_map_mul`), commute with the matrix units
(`rho_commute`), are the Tate action on `G_{L'}` (`rho_eq_act`); C2
(`PkgI3.C2_absolutelyIrreducible`) applied to `splitEquiv` makes `ρ|_W` absolutely irreducible on
`G_{L'}`. -/
theorem g8 (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate) (hT : PkgI3.TateModuleFree)
    (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange) (hM : G8Matrix)
    {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ))
    (h7 : G7Out A ℓ Tm c ε a β u) :
    ∃ r : GaloisRep ℓ 2, G8Out A ℓ (GlueDescent.rho Tm a β) r := by
  obtain ⟨hdim, hrank, hTm, ha, hβ, hβ0, hres, hcomm, hcont⟩ := h7
  -- the descended representation
  have h1 : GlueDescent.rho Tm a β 1 = 1 := by
    have := hres 1
    rw [map_one] at this
    refine (GlueDescent.rho_eq_act Tm (fun _ => tate A ℓ 1) a β 1 this.1 this.2.1 this.2.2).trans ?_
    exact map_one (tate A ℓ)
  let ρ : Representation (PadicAlgCl ℓ) PkgI4.GQ (Vb A ℓ) :=
    GlueDescent.rhoRep Tm c ε a β hTm ha hβ hβ0 h1
  have hρ : ∀ g, ρ g = GlueDescent.rho Tm a β g := fun _ => rfl
  have hρres : ∀ σ, ρ (resQ K σ) = tate A ℓ σ := fun σ =>
    GlueDescent.rho_eq_act Tm (fun _ => tate A ℓ σ) a β (resQ K σ) (hres σ).1 (hres σ).2.1
      (hres σ).2.2
  have hc : ∀ g i j, Commute (ρ g) (u.e i j) := fun g i j =>
    GlueDescent.rho_commute Tm a β (u.e i j) (fun g => hcomm g i j) g
  -- finite-dimensionality of `ℚ̄_ℓ ⊗ V_ℓ(A)`
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓK
  haveI : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := inferInstance
  haveI : FiniteDimensional (PadicAlgCl ℓ) (Vb A ℓ) := inferInstance
  -- `dim = 4`, so `W ≠ 0`
  have h4 : Module.finrank (PadicAlgCl ℓ) (Vb A ℓ) = 4 := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange]
    rw [hdim] at hrk
    have h22 : (2 : WithBot ℕ∞) * 2 = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      norm_num
    rw [h22] at hrk
    exact_mod_cast hrk
  haveI hVne : Nontrivial (Vb A ℓ) :=
    Module.nontrivial_of_finrank_pos (R := PadicAlgCl ℓ) (by omega)
  haveI : Nontrivial u.W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    haveI := hW
    haveI : Subsingleton (u.W × u.W) := inferInstance
    exact not_subsingleton (Vb A ℓ) u.splitEquiv.toEquiv.subsingleton
  -- C2 on `G_K`
  let rW : Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) u.W :=
    (restrictRep ρ u.W (fun g _ hw => u.mapsTo_W ρ hc g hw)).comp (resQ K)
  have he : ∀ σ v, u.splitEquiv (tate A ℓ σ v) = (rW σ).prodMap (rW σ) (u.splitEquiv v) := by
    intro σ v
    rw [← hρres σ, u.splitEquiv_intertwines ρ hc]
    rfl
  have hirr := fun (F : Type) [Field F] [Algebra (PadicAlgCl ℓ) F] =>
    PkgI3.C2_absolutelyIrreducible hS hF hT hH hSS A ℓ hrank (PadicAlgCl ℓ) rW u.splitEquiv he F
  obtain ⟨r, e, hint, hadj⟩ := hM K A ℓ ρ u hc h4 (fun f v => by simpa [hρ] using hcont f v)
    hirr
  exact ⟨r, hρres, e, hint, hadj⟩

/-- **G11 (proved from `G2Out`, `G3Out` and G8's intertwining, no further glue).** At `p ∉ T`,
`p ≠ ℓ`, an inertia element `σ` above `p` lies in `G_K` (G2), acts trivially on `V_ℓ(A)` (G3 with
R7a), hence trivially on `r ⊕ r`, hence `r(σ) = 1`. -/
theorem g11 {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Finset ℕ) (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h2 : G2Out K T) (h3 : G3Out A ℓ T)
    (hint : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) : G11Out T r := by
  intro p hp hpT hpℓ v hv σ hσ
  obtain ⟨σ', hσ'⟩ := MonoidHom.mem_range.mp (h2 p hp hpT v hv σ hσ)
  have ht := h3 p hp hpT hpℓ v hv σ' ⟨σ, hσ, hσ'.symm⟩
  have key : ∀ w : Fin 2 → PadicAlgCl ℓ, (r.mat (resQ K σ')).mulVec w = w := by
    intro w
    have := hint σ' (e.symm (w, 0))
    rw [ht] at this
    simp only [Module.End.one_apply, LinearEquiv.apply_symm_apply] at this
    exact (congrArg Prod.fst this).symm
  have hM : r.mat (resQ K σ') = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, key, Matrix.one_mulVec]
  rw [← hσ']
  exact Units.ext hM

/-- G11 gives Pan's "ramified at finitely many primes" (`S = T ∪ {ℓ}`). -/
theorem finitelyRamified_of_g11 {ℓ : ℕ} [Fact ℓ.Prime] {T : Finset ℕ} {r : GaloisRep ℓ 2}
    (h : G11Out T r) : r.FinitelyRamified :=
  ⟨insert ℓ T, fun p hp hpS => h p hp (fun h' => hpS (Finset.mem_insert_of_mem h'))
    (fun h' => hpS (h' ▸ Finset.mem_insert_self ℓ T))⟩

/-- Absolute irreducibility on `G_K` (G8) gives Pan's irreducibility on `G_ℚ`. -/
theorem isIrreducible_of_g8 {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2}
    (hadj : Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤) :
    r.IsIrreducible := by
  unfold PkgI4.GaloisRep.IsIrreducible
  rw [eq_top_iff, ← hadj]
  apply Algebra.adjoin_mono
  rintro _ ⟨σ, rfl⟩
  exact ⟨_, rfl⟩

/-- **G12 (proved from Pan∘Berger (R11+R12), the weight comparison `PkgI4.weight_match`, the
determinant argument `GlueAssembly.twist_finite`, and the named pieces `G12Weight`, `G12Det`).**
The hypotheses of Pan's Theorem 1.0.4 at `p = 5` come from G8 (irreducible), G11 (finitely
ramified), G9 (de Rham, distinct weights `0 ≠ −1`) and G10 (odd). -/
theorem g12 (hPB : PkgI4.PanBerger) (hR14 : HSyn.EigenformRepExists) (hR13 : PkgI4.EigenformHT)
    (hR15 : HSyn.DeligneSerreConseq) (hT18 : HSyn.FrobeniusDense) (hT19 : HSyn.BrauerNesbitt)
    (hT9 : LeafPush.T09_WeilPairing.{0}) (hW : G12Weight) (hD : G12Det)
    {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (T : Finset ℕ) (r : GaloisRep 5 2)
    (e : Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (hdim : A.dim = 2) (hint : Intertwines (tate A 5) (fun σ => r.mat (resQ K σ)) e)
    (hirr : r.IsIrreducible) (h9 : G9Out r) (h10 : G10Out r) (h11 : G11Out T r) :
    G12Out r := by
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, ιC, ιL, S, hatt⟩ :=
    hPB 5 (le_refl 5) r hirr (finitelyRamified_of_g11 h11) h9.1 h10 ⟨0, -1, by norm_num, h9.2⟩
  obtain ⟨n, hn⟩ := hW hR14 hR13 hR15 hT18 hT19 r N k χ g ψ ιC ιL S hN hk hg hirr h9.2 hatt
  obtain ⟨-, rfl⟩ := PkgI4.weight_match n k hk hn
  obtain ⟨H, hH, dr, εg, χc, hdet, hHsq, hε⟩ :=
    hD hR14 hT9 K A r e N χ g ψ ιC ιL S hdim hint hN hg hatt
  haveI := hH
  exact ⟨N, χ, g, ψ, ιC, ιL, S, hN, hg,
    GlueAssembly.twist_finite H dr εg χc ψ.toHom hdet hHsq hε, hatt⟩

/-- **G8-G11 at every coefficient prime `ℓ` (proved from the leaves, the outputs `G2Out`,
`G3Out`, `G6Out`, `G7Out`, and the named glue `G8Matrix`, `G9Glue`, `G10Glue`).** -/
theorem g8_g11 (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate)
    (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hR10 : PkgI4.DeRhamComparison) (hT23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p)
    (hT11 : HSyn.T11_RiemannGAGA) (hT12 : HSyn.T12_ArtinComparison)
    (hM : G8Matrix) (h9g : G9Glue) (h10g : G10Glue)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (ℓ : ℕ) [Fact ℓ.Prime] (h3 : G3Out A ℓ T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ))
    (h7 : G7Out A ℓ Tm c ε a β u) :
    ∃ r : GaloisRep ℓ 2, G8Out A ℓ (GlueDescent.rho Tm a β) r ∧ G9Out r ∧ G10Out r ∧
      G11Out T r := by
  have hdim := h7.1
  have hrank := h7.2.1
  obtain ⟨r, hres, e, hint, hadj⟩ := g8 hS hF hT hH hSS hM A ℓ Tm c ε a β u h7
  have hintK := intertwines_res hres hint
  exact ⟨r, ⟨hres, e, hint, hadj⟩, h9g hR10 hT23 K A ℓ r e hdim hintK,
    h10g hT11 hT12 hF K A ℓ r e hdim hrank h6.1 h6.2 hintK, g11 A ℓ T r e h2 h3 hintK⟩

/-- **G8-G12 at `ℓ = 5`: the conclusion of this range** (proved from the leaves, the outputs of
G2, G3, G6, G7, and the five named glue pieces). It is the input of G13 (g0-mod-newform's range):
`r₅` with `ℚ̄₅ ⊗ V₅(A) ≅ r₅|G_{L'} ⊕ r₅|G_{L'}` and `r₅` attached up to a finite twist to a
weight-2 eigenform. -/
theorem g8_g12 (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate)
    (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hR10 : PkgI4.DeRhamComparison) (hT23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p)
    (hT11 : HSyn.T11_RiemannGAGA) (hT12 : HSyn.T12_ArtinComparison)
    (hPB : PkgI4.PanBerger) (hR14 : HSyn.EigenformRepExists) (hR13 : PkgI4.EigenformHT)
    (hR15 : HSyn.DeligneSerreConseq) (hT18 : HSyn.FrobeniusDense) (hT19 : HSyn.BrauerNesbitt)
    (hT9 : LeafPush.T09_WeilPairing.{0})
    (hM : G8Matrix) (h9g : G9Glue) (h10g : G10Glue) (hW : G12Weight) (hD : G12Det)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r ∧ G9Out r ∧ G10Out r ∧
      G11Out T r ∧ G12Out r := by
  obtain ⟨r, h8, h9, h10, h11⟩ :=
    g8_g11 hS hF hT hH hSS hR10 hT23 hT11 hT12 hM h9g h10g A T h2 h6 5 h3 Tm c ε a β u h7
  obtain ⟨hres, e, hint, hadj⟩ := h8
  exact ⟨r, ⟨hres, e, hint, hadj⟩, h9, h10, h11,
    g12 hPB hR14 hR13 hR15 hT18 hT19 hT9 hW hD A T r e h7.1 (intertwines_res hres hint)
      (isIrreducible_of_g8 hadj) h9 h10 h11⟩

end G0Galois

end

end G0GaloisSec
