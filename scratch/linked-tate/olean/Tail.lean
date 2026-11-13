import LPrefix


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
(g0-assemble: the hypotheses `HSyn.T11_RiemannGAGA → HSyn.T12_ArtinComparison →` of g0-mod-galois'
text were opaque placeholders, removed from `Leaves.lean` by leaf-adopt2; they are replaced by
leaf-push2's concrete T11 leaves `T11a_RiemannEnd`, `T11b_Rigidity` (bundle fields `t11a`, `t11b`).
T12 is glue since leaf-adopt2, so its content is part of what this glue Prop asserts.)
(This is N5 L742-751's Betti argument; the rank/division/noncommutativity hypotheses are not
needed by it but are kept, being true for Glazer's `A`.) -/
def G10Glue : Prop :=
  ZInQ.LeafPush2.T11a_RiemannEnd → ZInQ.LeafPush2.T11b_Rigidity → PkgI3.FaltingsTate →
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
    (hT11 : ZInQ.LeafPush2.T11a_RiemannEnd) (hT12 : ZInQ.LeafPush2.T11b_Rigidity)
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
    (hT11 : ZInQ.LeafPush2.T11a_RiemannEnd) (hT12 : ZInQ.LeafPush2.T11b_Rigidity)
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

/-! ### G8's linear-algebra remainder, reduced to Burnside's theorem -/

section G0GaloisMatrixSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep)

/-- **Burnside's theorem, absolutely irreducible form (textbook leaf; Lang, *Algebra*, XVII §3,
Cor. 3.4, and Curtis–Reiner §27 (Burnside, Frobenius–Schur); locators UNVERIFIED).** If a
finite-dimensional representation `ρ` of a monoid over a field `F` stays irreducible after every
field extension, then the matrices `ρ(g)` (in any basis) generate `M_n(F)` as an `F`-algebra.
Mathlib has the Jacobson density theorem (`jacobson_density`), from which it follows. -/
def BurnsideAbsIrred : Prop :=
  ∀ (F : Type) [Field F] (G : Type) [Monoid G] (W : Type) [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (n : ℕ) (b : Module.Basis (Fin n) F W) (ρ : Representation F G W),
    (∀ (F' : Type) [Field F'] [Algebra F F'], (GlueI3.repBaseChange F' ρ).IsIrreducible) →
    Algebra.adjoin F (Set.range fun g => LinearMap.toMatrix b b (ρ g)) = ⊤

/-- **`G8Matrix` from Burnside (proved).** A basis of `W = e₀₀ V` (`dim W = 2`) turns `ρ|_W` into
a continuous `r : G_ℚ → GL₂(ℚ̄_ℓ)` (continuity from the weak continuity of `ρ`, through the
functionals `b.coord i ∘ e₀₀`); `splitEquiv` composed with the basis intertwines `ρ` with
`r ⊕ r`; Burnside gives the generation of `M₂(ℚ̄_ℓ)` by `r(G_K)`. -/
theorem g8Matrix_of_burnside (hB : BurnsideAbsIrred) : G8Matrix := by
  intro K _ _ A ℓ _ ρ u hc h4 hcont hirr
  haveI : FiniteDimensional (PadicAlgCl ℓ) (Vb A ℓ) :=
    Module.finite_of_finrank_pos (by rw [h4]; norm_num)
  have hW2 : Module.finrank (PadicAlgCl ℓ) u.W = 2 := u.finrank_W h4
  let b : Module.Basis (Fin 2) (PadicAlgCl ℓ) u.W :=
    Module.finBasisOfFinrankEq (PadicAlgCl ℓ) u.W hW2
  let rW := restrictRep ρ u.W (fun g _ hw => u.mapsTo_W ρ hc g hw)
  let m : PkgI4.GQ →* Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp rW
  have hm : ∀ g, m g = LinearMap.toMatrix b b (rW g) := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply]
    exact LinearMap.toMatrixAlgEquiv_apply b (rW g) i j
  have hcm : Continuous fun g => m g := by
    refine continuous_matrix fun i j => ?_
    let f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ) :=
      (b.coord i).comp ((u.e 0 0).codRestrict u.W (fun v => u.mem_W_of_e0 0 v))
    refine (hcont f (b j : Vb A ℓ)).congr fun g => ?_
    rw [hm, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
    change b.coord i _ = b.coord i _
    congr 1
    exact Subtype.ext (u.e00_of_mem (u.mapsTo_W ρ hc g (b j).2))
  let toHom : PkgI4.GQ →* GL (Fin 2) (PadicAlgCl ℓ) := m.toHomUnits
  have hcont' : Continuous toHom := by
    rw [Units.continuous_iff]
    refine ⟨hcm, ?_⟩
    have hinv : (fun g => (((toHom g)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) :
        Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))) = fun g => m g⁻¹ := by
      funext g
      rw [← map_inv]
      rfl
    rw [hinv]
    exact hcm.comp continuous_inv
  let r : GaloisRep ℓ 2 := ⟨toHom, hcont'⟩
  have hrmat : ∀ g, r.mat g = LinearMap.toMatrix b b (rW g) := hm
  let e := u.splitEquiv.trans (b.equivFun.prodCongr b.equivFun)
  refine ⟨r, e, ?_, ?_⟩
  · intro g v
    have h1 := u.splitEquiv_intertwines ρ hc g v
    simp only [e, LinearEquiv.trans_apply, h1, LinearEquiv.prodCongr_apply,
      Module.Basis.equivFun_apply, hrmat]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [LinearMap.toMatrix_mulVec_repr]
      rfl
    · dsimp only
      rw [LinearMap.toMatrix_mulVec_repr]
      rfl
  · have hfun : (fun σ => r.mat (resQ K σ)) =
        fun σ => LinearMap.toMatrix b b ((rW.comp (resQ K)) σ) :=
      funext fun σ => hrmat _
    rw [hfun]
    exact hB (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) u.W 2 b (rW.comp (resQ K)) hirr

end G0Galois

end

end G0GaloisMatrixSec

/-! ### G12's determinant identities (`G12Det`), split into R14's determinant clause, `DetTate`
and `ResQFiniteIndex` -/

section G0GaloisDetSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- `σ ↦ σ` as ring automorphisms of `ℚ̄`. -/
def toRingEquivQ : PkgI4.GQ →* (PkgI4.Qbar ≃+* PkgI4.Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `ℓ`-adic cyclotomic character `χ_ℓ : G_ℚ → ℤ_ℓ^× ⊆ ℚ̄_ℓ^×` (Mathlib's
`cyclotomicCharacter` on `ℚ̄`, as `PkgI4.cyc` on `G_{ℚ_p}`). -/
def cycQ (ℓ : ℕ) [Fact ℓ.Prime] : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter PkgI4.Qbar ℓ).comp toRingEquivQ)

/-- **R14 with its published determinant clause (leaf; Shimura 1971 Thm 7.14 for `k = 2`,
Deligne 1971 for `k ≥ 2`, Deligne–Serre 1974 for `k = 1`; locators UNVERIFIED).** For a normalized
eigenform `g` of weight `k ≥ 1` with nebentypus, there is a semisimple `ρ_g` attached to `g` with
`det ρ_g = ε · χ_ℓ^{k−1}`, `ε` of finite image (the nebentypus as a Galois character). This is
`HSyn.EigenformRepExists` plus the determinant, which the published statements contain. -/
def R14Det : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k),
    0 < N → 1 ≤ k → PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
      ∃ ε : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
        ∀ σ, (ρ.mat σ).det = ((ε σ * cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

/-- **`det V_ℓ(A) = χ_ℓ^{dim A}` (GLUE, unproved; from T9, the Weil pairing of a polarization:
`G_K` acts on `V_ℓ(A)` through `GSp_{2g}` with multiplier `χ_ℓ`, Mumford §20, §23, STANDARD).** -/
def DetTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ),
    A.dim = g → ∀ σ, LinearMap.det (tate A ℓ σ) = ((cycQ ℓ (resQ K σ) : PadicAlgCl ℓ)) ^ g

/-- **`G_K` has finite index in `G_ℚ` (GLUE, unproved; Galois theory: the index is `[K:ℚ]`).** -/
def ResQFiniteIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], (resQ K).range.FiniteIndex

/-- **Chebotarev density, PkgI4 form** (copied verbatim from scratch/c9-rhof, where it is
`HSyn.FrobeniusDense` with pkg-I4's `LiesOver`, `IsArithFrob`; leaf T18). -/
def FrobeniusDenseQ : Prop :=
  ∀ (U : Subgroup PkgI4.GQ), IsOpen (U : Set PkgI4.GQ) → ∀ (σ : PkgI4.GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
      PkgI4.LiesOver v p ∧ PkgI4.IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- The bundle's T18 is `FrobeniusDenseQ` (the two `LiesOver`, `IsArithFrob` have equal bodies). -/
theorem frobeniusDenseQ_of (h : HSyn.FrobeniusDense) : FrobeniusDenseQ := h

/-- (copied from scratch/c9-rhof, proved there from T18) Continuous functions agreeing at
arithmetic Frobenius elements outside `S` are equal. -/
theorem eq_of_eq_on_arithFrob (hD : FrobeniusDenseQ) {X : Type*} [TopologicalSpace X]
    [T2Space X] (S : Finset ℕ) (f₁ f₂ : PkgI4.GQ → X) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
      PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → f₁ τ = f₂ τ) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : PkgI4.GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ PkgI4.Qbar _).mp hmem
  have hU : IsOpen (E.fixingSubgroup : Set PkgI4.GQ) := IntermediateField.fixingSubgroup_isOpen E
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := hD E.fixingSubgroup hU g S
  have hfix : g⁻¹ * τ ∈ E.fixingSubgroup := by
    have := E.fixingSubgroup.inv_mem hU'
    simpa using this
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_ofPred_eq] at this
  exact this (hfr p hp hpS v τ hv hτ)

/-- `det M = (tr(M)² − tr(M²))/2` for `2 × 2` matrices in characteristic `0`. -/
theorem det_fin_two_eq_trace {R : Type*} [Field R] [CharZero R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.det = ((M.trace) ^ 2 - (M * M).trace) / 2 := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

theorem continuous_mat {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r : GaloisRep ℓ n) :
    Continuous fun x => r.mat x :=
  Units.continuous_val.comp r.continuous_toHom

/-- **`G12Det` (proved from R14Det, DetTate, ResQFiniteIndex and T18).** `det r = det(ρ_g ⊗ ψ)`
everywhere (traces agree at Frobenius, hence everywhere by T18; then the `2 × 2` identity), and
`(det r)² = det V₅(A) = χ₅²` on `G_K` (through `e`, `LinearMap.det_conj`, `det_prodMap`). -/
theorem g12Det_of (hR : R14Det) (hDT : DetTate) (hFI : ResQFiniteIndex)
    (hD : FrobeniusDenseQ) : G12Det := by
  intro _ _ K _ _ A r e N χ g ψ ιC ιL S hdim hint hN hg hatt
  obtain ⟨ρ, -, hρatt, ε, hεfin, hdet⟩ := hR 5 ιC ιL N 2 χ g hN (by norm_num) hg
  -- traces of `r` and `ψ ⊗ ρ_g` agree
  have hN5 : N * 5 ≠ 0 := by positivity
  have htr : ∀ x, (r.mat x).trace = (ψ.toHom x : PadicAlgCl 5) * (ρ.mat x).trace := by
    have h := eq_of_eq_on_arithFrob hD (S ∪ (N * 5).primeFactors) (fun x => (r.mat x).trace)
      (fun x => (ψ.toHom x : PadicAlgCl 5) * (ρ.mat x).trace)
      (continuous_mat r).matrix_trace
      ((Units.continuous_val.comp ψ.continuous_toHom).mul (continuous_mat ρ).matrix_trace)
      (by
        intro p hp hpS v τ hv hτ
        have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
        have hpN : ¬ p ∣ N * 5 := fun h =>
          hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hN5⟩))
        obtain ⟨-, α, hα, hαt⟩ := hatt p hp hpS1
        obtain ⟨-, α', hα', hα't⟩ := hρatt p hp hpN
        have hαα : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
        rw [hαt v τ hv hτ, hα't v τ hv hτ, hαα])
    exact fun x => congrFun h x
  have hmul : ∀ {n : ℕ} (q : GaloisRep 5 n) x, q.mat (x * x) = q.mat x * q.mat x := by
    intro n q x
    simp [PkgI4.GaloisRep.mat, map_mul]
  have hdetr : ∀ x, (r.mat x).det = (ψ.toHom x : PadicAlgCl 5) ^ 2 * (ρ.mat x).det := by
    intro x
    have h1 := htr x
    have h2 := htr (x * x)
    rw [hmul r x, hmul ρ x, map_mul, Units.val_mul] at h2
    rw [det_fin_two_eq_trace (r.mat x), det_fin_two_eq_trace (ρ.mat x), h1, h2]
    ring
  haveI := hFI K
  refine ⟨(resQ K).range, inferInstance, Matrix.GeneralLinearGroup.det.comp r.toHom, ε,
    cycQ 5, ?_, ?_, hεfin⟩
  · intro x
    apply Units.ext
    have hx := hdetr x
    rw [hdet x] at hx
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul,
      Units.val_pow_eq_pow_val]
    change (r.mat x).det = _
    rw [hx]
    norm_num
    ring
  · rintro _ ⟨σ, rfl⟩
    apply Units.ext
    have hconj : ((e : Vb A 5 →ₗ[PadicAlgCl 5] _) ∘ₗ tate A 5 σ ∘ₗ
        (e.symm : _ →ₗ[PadicAlgCl 5] Vb A 5)) =
        (Matrix.toLin' (r.mat (resQ K σ))).prodMap (Matrix.toLin' (r.mat (resQ K σ))) := by
      apply LinearMap.ext
      intro w
      have := hint σ (e.symm w)
      simp only [LinearEquiv.apply_symm_apply] at this
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
        LinearMap.prodMap_apply, Matrix.toLin'_apply]
    have h := LinearMap.det_conj (tate A 5 σ) e
    rw [hconj, LinearMap.det_prodMap, LinearMap.det_toLin', hDT K A 5 2 hdim σ] at h
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_pow_eq_pow_val]
    change (r.mat (resQ K σ)).det ^ 2 = _
    rw [← h]
    ring

end G0Galois

end

end G0GaloisDetSec


/-! ### g0-mod-galois: the range G8-G12 from the leaf bundles -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

noncomputable section

/-- The pieces of the range G8-G12 that are not in the leaf bundles: Burnside (a textbook leaf;
`G8Matrix` is proved from it, `g8Matrix_of_burnside`), R14's determinant clause (a leaf, R14 as
published), and the named glue `G9Glue`, `G10Glue`, `G12Weight`, `DetTate`, `ResQFiniteIndex`
(`G12Det` is proved from the last two, R14Det and T18, `g12Det_of`). -/
structure GaloisPieces : Prop where
  burnside : BurnsideAbsIrred
  r14det : R14Det
  deRham : G9Glue
  odd : G10Glue
  weight : G12Weight
  detTate : DetTate
  finIndex : ResQFiniteIndex

/-- **G8-G12 from the leaf bundles** (`HSyn.ResearchLeaves`, `HSyn.TextbookLeaves`), glue-ssbc's
proved `SemisimpleBaseChange`, the outputs of G2, G3, G6, G7 and the five named pieces. -/
theorem g8_g12_of_leaves (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves) (m : GaloisPieces)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅ :=
  g8_g12 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a t.t11b
    r.r11r12 r.r14 r.r13 r.r15 t.frobeniusDense HSyn.t19_proved t.t9 (g8Matrix_of_burnside m.burnside) m.deRham m.odd m.weight
    (g12Det_of m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.frobeniusDense))
    A T h2 h6 h3 Tm c ε a β u h7

/-! ### How the conclusion feeds G13-G16 and `ModularConstituent` -/

/-- **What G13-G16 must deliver on the `J₁(N)` side** (input of the link lemma below): an
injective `G_K`-equivariant map from `r|G_K` (the matrices `r(σ)`, `σ ∈ G_K`, on `ℚ̄₅²`) into
`ℚ̄₅ ⊗ V₅(J)`, for `J = J₁(N)_{L'}` (G13: `r₅ ≅ ρ_{f,5}` and `ρ_{f,5} ⊂ V₅(J₁(N))`, R16). -/
def JSide {K : Type} [Field K] [NumberField K] (J : PkgI3.AbVar K) (r : GaloisRep 5 2) : Prop :=
  ∃ ιJ : (Fin 2 → PadicAlgCl 5) →ₗ[PadicAlgCl 5] Vb J 5, Function.Injective ιJ ∧
    ∀ σ w, tate J 5 σ (ιJ w) = ιJ ((r.mat (resQ K σ)).mulVec w)

/-- **Link lemma (proved).** G8's output (`ℚ̄₅ ⊗ V₅(A) ≅ r|G_K ⊕ r|G_K`) and the `J`-side of
G13-G16 (`JSide`) give `CommonConstituent A J`, the field of `ModularConstituent` that E1
(`PkgI3.E1_exists_hom_ne_zero`) consumes, with `ℓ = 5` and `E = ℚ̄₅`. -/
theorem commonConstituent_of_sides {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K)
    (r : GaloisRep 5 2)
    (e : Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (hint : Intertwines (tate A 5) (fun σ => r.mat (resQ K σ)) e) (hJ : JSide J r) :
    HSyn.G0Split.CommonConstituent A J := by
  obtain ⟨ιJ, hιJ, hJeq⟩ := hJ
  let ιA : (Fin 2 → PadicAlgCl 5) →ₗ[PadicAlgCl 5] Vb A 5 :=
    e.symm.toLinearMap ∘ₗ LinearMap.inl (PadicAlgCl 5) _ _
  have hιA : Function.Injective ιA := e.symm.injective.comp LinearMap.inl_injective
  have hAeq : ∀ σ w, tate A 5 σ (ιA w) = ιA ((r.mat (resQ K σ)).mulVec w) := by
    intro σ w
    apply e.injective
    have h := hint σ (ιA w)
    simp only [ιA, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.inl_apply, LinearEquiv.apply_symm_apply] at h ⊢
    rw [h, Matrix.mulVec_zero]
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl 5) (A.galRep 5)) :=
    ⟨LinearMap.range ιA, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hAeq σ w).symm⟩⟩
  let U' : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl 5) (J.galRep 5)) :=
    ⟨LinearMap.range ιJ, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hJeq σ w).symm⟩⟩
  have keyA : ∀ w (h : ιA w ∈ U.toSubmodule),
      (LinearEquiv.ofInjective ιA hιA).symm ⟨ιA w, h⟩ = w := by
    intro w h
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    first
      | rfl
      | exact (LinearEquiv.ofInjective_apply (h := hιA) w).symm
  refine ⟨5, inferInstance, PadicAlgCl 5, inferInstance, inferInstance, U, U',
    (LinearEquiv.ofInjective ιA hιA).symm.trans (LinearEquiv.ofInjective ιJ hιJ), ?_, ?_⟩
  · intro h
    have h' : ιA (Pi.single 0 1) ∈ U.toSubmodule := ⟨_, rfl⟩
    rw [h] at h'
    have h0 : ιA (Pi.single 0 1) = 0 := h'
    have := hιA (h0.trans (map_zero ιA).symm)
    have := congrFun this 0
    simp at this
  · rintro σ ⟨_, w, rfl⟩
    have hmem : ιA ((r.mat (resQ K σ)).mulVec w) ∈ U.toSubmodule := ⟨_, rfl⟩
    have hx : (⟨GlueI3.repBaseChange (PadicAlgCl 5) (A.galRep 5) σ (ιA w),
        U.apply_mem_toSubmodule σ ⟨w, rfl⟩⟩ : U.toSubmodule) = ⟨_, hmem⟩ :=
      Subtype.ext (hAeq σ w)
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hx, keyA]
    first
      | (erw [keyA]; exact (hJeq σ w).symm)
      | (simp only [keyA]; exact (hJeq σ w).symm)

/-! ### Feeding g0-mod-newform's `G12Out` (G13-G16's input)

The next four definitions are copied verbatim from `scratch/g0-mod-newform/part_new.lean`
(commit 217e17f0), where they are G13's input interface. -/

namespace NF

/-- (copied from g0-mod-newform) `ρ` as a `Representation` on `ℚ̄_ℓⁿ`. -/
def toRep {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ : GaloisRep ℓ n) :
    Representation (PadicAlgCl ℓ) PkgI4.GQ (Fin n → PadicAlgCl ℓ) where
  toFun σ := Matrix.toLin' (ρ.mat σ)
  map_one' := by
    simp only [PkgI4.GaloisRep.mat, map_one, Units.val_one, Matrix.toLin'_one]; rfl
  map_mul' σ τ := by
    simp only [PkgI4.GaloisRep.mat, map_mul, Units.val_mul, Matrix.toLin'_mul]; rfl

/-- (copied from g0-mod-newform) Pan-Berger's output on `r`, with the twist a Dirichlet
character at arithmetic Frobenius outside `S`. -/
def PanOutput {ℓ : ℕ} [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (r : GaloisRep ℓ 2) : Prop :=
  ∃ (M : ℕ) (χg : DirichletCharacter ℂ M) (g : PkgI4.CF M 2) (m : ℕ)
    (ψD : DirichletCharacter ℂ m) (ψ : GaloisChar ℓ) (S : Finset ℕ),
    0 < M ∧ PkgI4.IsNormalizedEigenform g χg ∧ 0 < m ∧ r.AttachedUpToTwist ψ ιC ιL g S ∧
    ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : PkgI4.Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ), PkgI4.LiesOver v p →
        PkgI4.IsArithFrob τ v p → (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- (copied from g0-mod-newform) `r|_{G_L}` is a constituent of `V_ℓ(A) ⊗ ℚ̄_ℓ`. -/
def IsConstituentOf (ℓ : ℕ) [Fact ℓ.Prime] {L : Type} [Field L] [Algebra ℚ L]
    (A : PkgI3.AbVar L) (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L)
    (r : GaloisRep ℓ 2) : Prop :=
  ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ)), U ≠ ⊥ ∧
    ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : PkgI4.GQ), (∀ x, i (σ x) = τ (i x)) →
      ∀ u : U.toSubmodule,
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u, U.apply_mem_toSubmodule τ u.2⟩ =
          toRep r σ (e u)

/-- (copied from g0-mod-newform) The data that G8-G12 produce for the model `A/L'`. -/
structure ModData (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L
  ιC : PkgI4.Qbar →ₐ[ℚ] ℂ
  ι5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3
  r5 : GaloisRep 5 2
  r3 : GaloisRep 3 2

instance fact_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- (copied from g0-mod-newform) G13's input on the data `D`. -/
def G12Spec {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) : Prop :=
  D.r5.IsIrreducible ∧ D.r3.IsIrreducible ∧ IsConstituentOf 5 A D.i D.r5 ∧
    IsConstituentOf 3 A D.i D.r3 ∧ PanOutput D.ιC D.ι5 D.r5

/-- (copied from g0-mod-newform, there `G12Out`) some data `D` for `A` satisfy `G12Spec`. -/
def NewformG12Out {L : Type} [Field L] [NumberField L] (A : PkgI3.AbVar L) : Prop :=
  ∃ D : ModData L A, G12Spec D

end NF

/-- **Finite characters are Dirichlet characters (GLUE, unproved; h-trust C8 item 4).** From T17
(Kronecker–Weber): a continuous `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius
elements above `p ∉ S` (`S` the primes dividing the conductor `m`), the image under `ιL` of an
algebraic number `β` (a root of unity) with `ιC(β) = ψD(p)` for a Dirichlet character `ψD`
mod `m`. True: the kernel field of `ψ` is finite abelian over `ℚ`, hence inside `ℚ(ζ_m)`; the
values are roots of unity, which lie in `ιL(ℚ̄)`. -/
def FiniteCharDirichlet : Prop :=
  HSyn.KroneckerWeber →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ψ : GaloisChar ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ), (Set.range ψ.toHom).Finite →
    ∃ (m : ℕ) (ψD : DirichletCharacter ℂ m) (S : Finset ℕ), 0 < m ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : PkgI4.Qbar, ιC β = ψD (p : ZMod m) ∧
        ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ), PkgI4.LiesOver v p →
          PkgI4.IsArithFrob τ v p → (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **G8's output gives g0-mod-newform's constituent clause (proved).** With `i = qEmb K`, the
`σ` with `i ∘ σ = τ ∘ i` is `resQ K τ` (`eq_resQ`), so G8's intertwining is `IsConstituentOf`. -/
theorem isConstituentOf_of_intertwines {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hint : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    NF.IsConstituentOf ℓ A (qEmb K) r := by
  let ιA : (Fin 2 → PadicAlgCl ℓ) →ₗ[PadicAlgCl ℓ] Vb A ℓ :=
    e.symm.toLinearMap ∘ₗ LinearMap.inl (PadicAlgCl ℓ) _ _
  have hιA : Function.Injective ιA := e.symm.injective.comp LinearMap.inl_injective
  have hAeq : ∀ σ w, tate A ℓ σ (ιA w) = ιA ((r.mat (resQ K σ)).mulVec w) := by
    intro σ w
    apply e.injective
    have h := hint σ (ιA w)
    simp only [ιA, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.inl_apply, LinearEquiv.apply_symm_apply] at h ⊢
    rw [h, Matrix.mulVec_zero]
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)) :=
    ⟨LinearMap.range ιA, by rintro σ _ ⟨w, rfl⟩; exact ⟨_, (hAeq σ w).symm⟩⟩
  have keyA : ∀ w (h : ιA w ∈ U.toSubmodule),
      (LinearEquiv.ofInjective ιA hιA).symm ⟨ιA w, h⟩ = w := by
    intro w h
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    first
      | rfl
      | exact (LinearEquiv.ofInjective_apply (h := hιA) w).symm
  refine ⟨U, (LinearEquiv.ofInjective ιA hιA).symm, ?_, ?_⟩
  · intro h
    have h' : ιA (Pi.single 0 1) ∈ U.toSubmodule := ⟨_, rfl⟩
    rw [h] at h'
    have h0 : ιA (Pi.single 0 1) = 0 := h'
    have := hιA (h0.trans (map_zero ιA).symm)
    have := congrFun this 0
    simp at this
  · rintro τ σ hσ ⟨_, w, rfl⟩
    have hστ := eq_resQ K τ σ hσ
    have hmem : ιA ((r.mat (resQ K τ)).mulVec w) ∈ U.toSubmodule := ⟨_, rfl⟩
    have hx : (⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ (ιA w),
        U.apply_mem_toSubmodule τ ⟨w, rfl⟩⟩ : U.toSubmodule) = ⟨_, hmem⟩ :=
      Subtype.ext (hAeq τ w)
    rw [hx, keyA]
    first
      | (erw [keyA]; subst hστ; rfl)
      | (simp only [keyA]; subst hστ; rfl)
      | (erw [keyA]; subst hστ; simp [NF.toRep, Matrix.toLin'_apply])
      | (simp only [keyA]; subst hστ; simp [NF.toRep, Matrix.toLin'_apply])

/-- **G12's output gives g0-mod-newform's `PanOutput` (proved from `FiniteCharDirichlet`).** -/
theorem panOutput_of_g12 (hKW : HSyn.KroneckerWeber) (hFD : FiniteCharDirichlet)
    (r : GaloisRep 5 2) (h : G12Out r) : ∃ ιC ιL, NF.PanOutput ιC ιL r := by
  obtain ⟨N, χ, g, ψ, ιC, ιL, S, hN, hg, hfin, hatt⟩ := h
  obtain ⟨m, ψD, S', hm, hD⟩ := hFD hKW 5 ψ ιC ιL hfin
  refine ⟨ιC, ιL, N, χ, g, m, ψD, ψ, S ∪ S', hN, hg, hm, ?_, ?_⟩
  · intro p hp hpS
    exact hatt p hp (fun h' => hpS (Finset.mem_union_left _ h'))
  · intro p hp hpS
    exact hD p hp (fun h' => hpS (Finset.mem_union_right _ h'))

/-- **The range G8-G12 delivers g0-mod-newform's input `G12Out` (there; here `NF.NewformG12Out`).**
Proved from the leaves, the outputs of G2, G3, G6, G7 at `ℓ = 3` and `ℓ = 5`, the five named
pieces of this range and `FiniteCharDirichlet`. -/
theorem newformG12Out_of_galois (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : GaloisPieces) (hKW : HSyn.KroneckerWeber) (hFD : FiniteCharDirichlet)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3₅ : G3Out A 5 T) (h3₃ : G3Out A 3 T)
    (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a₅ β₅ : PkgI4.GQ → PadicAlgCl 5)
    (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7₅ : G7Out A 5 Tm₅ c₅ ε₅ a₅ β₅ u₅)
    (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a₃ β₃ : PkgI4.GQ → PadicAlgCl 3)
    (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3) (Vb A 3))
    (h7₃ : G7Out A 3 Tm₃ c₃ ε₃ a₃ β₃ u₃) (ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3) :
    NF.NewformG12Out A := by
  obtain ⟨r₅, ⟨hres₅, e₅, hint₅, hadj₅⟩, -, -, -, h12⟩ :=
    g8_g12_of_leaves r t m A T h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, ⟨hres₃, e₃, hint₃, hadj₃⟩, -, -, -⟩ :=
    g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a t.t11b
      (g8Matrix_of_burnside m.burnside) m.deRham m.odd A T h2 h6 3 h3₃ Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨ιC, ι5, hpan⟩ := panOutput_of_g12 hKW hFD r₅ h12
  exact ⟨⟨qEmb K, ιC, ι5, ι3, r₅, r₃⟩, isIrreducible_of_g8 hadj₅, isIrreducible_of_g8 hadj₃,
    isConstituentOf_of_intertwines A 5 r₅ e₅ (intertwines_res hres₅ hint₅),
    isConstituentOf_of_intertwines A 3 r₃ e₃ (intertwines_res hres₃ hint₃), hpan⟩

end

end G0Galois


/-! ## Kernel copy: Part B-D of ZInQKernel/HDecomp/Conductor/LadicCond.lean (lines 180-765, verbatim; its Part A is the PkgI4 copy already above). Needed by g0-mod-newform. -/
section LadicCondSec
noncomputable section
set_option linter.unusedSectionVars false
/-! ## Part B. Inertia, ramification groups and the conductor exponent on `G_{ℚ_p}` -/

namespace LadicCond

open PkgI4

variable {p : ℕ} [Fact p.Prime]

/-- `ℚ̄_p` (Mathlib's `PadicAlgCl p`, normed by the unique extension of `|·|_p`). -/
abbrev Kbar (p : ℕ) [Fact p.Prime] := PadicAlgCl p

/-- A finite Galois extension `L/ℚ_p` inside `ℚ̄_p`. -/
abbrev Fld (p : ℕ) [Fact p.Prime] := IntermediateField ℚ_[p] (Kbar p)

/-- **Inertia** `I_p ⊂ G_{ℚ_p}`: the `σ` acting trivially on the residue field of `ℚ̄_p`,
i.e. `|σx − x| < 1` for all `|x| ≤ 1` (Serre, *Corps locaux* I §7 / IV §1). -/
def inertiaSet : Set (GQp p) := {σ | ∀ x : Kbar p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}

/-- **Wild inertia** `P_p ⊂ G_{ℚ_p}`: the `σ` with `σx/x ≡ 1` modulo the maximal ideal for all
`x ≠ 0`, i.e. `|σx − x| < |x|` (Serre, *Corps locaux* IV §2, Cor. 1 of Prop. 7, at every finite
level; UNVERIFIED numbering). -/
def wildSet : Set (GQp p) := {σ | ∀ x : Kbar p, x ≠ 0 → ‖σ x - x‖ < ‖x‖}

/-- `G_L ⊂ G_{ℚ_p}`: the `σ` fixing `L` pointwise. -/
def fixSet (L : Fld p) : Set (GQp p) := {σ | ∀ x ∈ L, σ x = x}

/-- `ϖ` is a uniformizer of `L`: an element of `L` of maximal absolute value `< 1`. -/
def IsUnif (L : Fld p) (ϖ : Kbar p) : Prop :=
  ϖ ∈ L ∧ ‖ϖ‖ < 1 ∧ ∀ y ∈ L, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖

/-- **Lower ramification groups** of `L/ℚ_p` (Serre, *Corps locaux* IV §1), pulled back to
`G_{ℚ_p}`: `σ ∈ ramSet L i` iff `v_L(σx − x) ≥ i + 1` for every `x ∈ 𝓞_L`. It contains `G_L`, and
its image under `σ ↦ σ|_L` is `G_i(L/ℚ_p)` (for `L/ℚ_p` Galois). -/
def ramSet (L : Fld p) (i : ℕ) : Set (GQp p) :=
  {σ | ∃ ϖ, IsUnif L ϖ ∧ ∀ x ∈ L, ‖x‖ ≤ 1 → ‖σ x - x‖ ≤ ‖ϖ‖ ^ (i + 1)}

/-- `σ ↦ σ|_L`, as a function `L → ℚ̄_p`. -/
def restr (L : Fld p) (σ : GQp p) : L → Kbar p := fun x => σ x

/-- `g_i = |G_i(L/ℚ_p)|`: the number of restrictions to `L` of elements of `ramSet L i`. -/
def ramCard (L : Fld p) (i : ℕ) : ℕ := Nat.card (restr L '' ramSet L i)

/-- `L/ℚ_p` is finite Galois. -/
def IsFinGal (L : Fld p) : Prop := FiniteDimensional ℚ_[p] L ∧ IsGalois ℚ_[p] L

variable {k : Type*} [Field k] {n : ℕ}

/-- `V^S` for `V = kⁿ` and a set `S ⊆ G_{ℚ_p}` acting through `ρ`. -/
def invariants (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) : Submodule k (Fin n → k) where
  carrier := {v | ∀ σ ∈ S, (ρ σ : Matrix (Fin n) (Fin n) k).mulVec v = v}
  zero_mem' := by intro σ _; simp
  add_mem' := by
    intro v w hv hw σ hσ
    simp only [Set.mem_ofPred_eq] at hv hw
    rw [Matrix.mulVec_add, hv σ hσ, hw σ hσ]
  smul_mem' := by
    intro c v hv σ hσ
    simp only [Set.mem_ofPred_eq] at hv
    rw [Matrix.mulVec_smul, hv σ hσ]

/-- `codim V^S = n − dim V^S`. -/
def codimInv (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) : ℕ :=
  n - Module.finrank k (invariants ρ S)

/-- `L` is **adapted** to `ρ`: `L/ℚ_p` is finite Galois and `ρ` is trivial on `P_p ∩ G_L`, so
that `ρ|_{P_p}` factors through `Gal(L/ℚ_p)`. For `ρ` continuous with values in `GL_n(E)`,
`E/ℚ_ℓ` finite, `ℓ ≠ p`, such an `L` exists, since `ρ(P_p)` is finite (`AdaptedExists`). -/
def IsAdapted (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : Prop :=
  IsFinGal L ∧ ∀ σ ∈ wildSet ∩ fixSet L, ρ σ = 1

/-- **The Swan conductor at level `L`** (Serre–Tate 1968 §2; Serre, *Corps locaux* VI §2):
`Sw_L(ρ) = ∑_{i ≥ 1} (g_i/g_0) · codim V^{G_i ∩ P}`. For `L` adapted, `G_i ∩ P` acts through
`G_i(L/ℚ_p)` (for `i ≥ 1`, `G_i(L/ℚ_p)` is the image of `P ∩ ramSet L i`). -/
def swanAt (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  ∑ᶠ i : ℕ, ((ramCard L (i + 1) : ℚ) / ramCard L 0) * (codimInv ρ (ramSet L (i + 1) ∩ wildSet) : ℚ)

open Classical in
/-- **The Swan conductor** `Sw(ρ)`: `swanAt L ρ` at a chosen adapted `L` (`0` if none exists,
which does not happen for continuous ℓ-adic `ρ`). Independent of `L`: `SwanIndependent`. -/
def swan (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  if h : ∃ L : Fld p, IsAdapted L ρ then swanAt h.choose ρ else 0

/-- **The conductor exponent** `a(ρ) = codim V^{I_p} + Sw(ρ)` (Serre–Tate 1968 §2; equal to the
conductor of the Weil–Deligne representation, `codim (ker N)^{I}` + Swan, since
`V^{ρ(I)} = (ker N)^{I}` by Grothendieck's monodromy theorem). -/
def condExp (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  codimInv ρ inertiaSet + swan ρ

/-- The conductor exponent computed at a level `L`. -/
def condAt (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  codimInv ρ inertiaSet + swanAt L ρ

/-- **Finite-level Artin conductor** (Serre, *Corps locaux* VI §2):
  `∑_{i ≥ 0} (g_i/g_0) codim V^{G_i}`.
For `ρ` trivial on `G_L` this is pkg-I6's `PkgI6.artinConductor` of the induced representation of
`Gal(L/ℚ_p)` (same formula, with `G_i(L/ℚ_p)` = image of `ramSet L i`). -/
def artinAt (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  ∑ᶠ i : ℕ, ((ramCard L i : ℚ) / ramCard L 0) * (codimInv ρ (ramSet L i) : ℚ)

/-! ### Herbrand's function and the upper numbering (for L8) -/

/-- Lower numbering for real `t`: `G_t = G_{⌈t⌉}` for `t > −1`, `G_t = G` for `t ≤ −1`. -/
def ramSetR (L : Fld p) (t : ℝ) : Set (GQp p) :=
  if t ≤ -1 then Set.univ else ramSet L ⌈t⌉.toNat

/-- `|G_t(L/ℚ_p)|` for real `t`. -/
def ramCardR (L : Fld p) (t : ℝ) : ℕ := Nat.card (restr L '' ramSetR L t)

/-- **Herbrand's function** `φ_{L/ℚ_p}(u) = ∫₀ᵘ g_t/g_0 dt` (Serre IV §3). -/
def phiAt (L : Fld p) (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)

/-- **Upper numbering** `G^v(L/ℚ_p) = G_{ψ(v)}`, `ψ = φ⁻¹` (Serre IV §3), pulled back to `G_{ℚ_p}`.
  -/
def upperSet (L : Fld p) (v : ℝ) : Set (GQp p) :=
  ramSetR L (sInf {u : ℝ | -1 ≤ u ∧ v ≤ phiAt L u})

/-- **The upper ramification filtration of `G_{ℚ_p}`**: `σ ∈ G^v` iff `σ|_L ∈ G^v(L/ℚ_p)` for
every finite Galois `L` (Serre IV §3, remark after Prop. 14; well defined by Herbrand's theorem). -/
def upperAbs (p : ℕ) [Fact p.Prime] (v : ℝ) : Set (GQp p) :=
  {σ | ∀ L : Fld p, IsFinGal L → σ ∈ upperSet L v}

/-! ## Part C. Sanity facts -/

theorem wildSet_subset_inertiaSet : (wildSet : Set (GQp p)) ⊆ inertiaSet := by
  intro σ hσ x hx
  by_cases h0 : x = 0
  · subst h0; simp
  · exact lt_of_lt_of_le (hσ x h0) hx

theorem invariants_eq_top {ρ : GQp p →* GL (Fin n) k} {S : Set (GQp p)}
    (h : ∀ σ ∈ S, ρ σ = 1) : invariants ρ S = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true]
  intro σ hσ
  rw [h σ hσ]
  simp

theorem codimInv_eq_zero {ρ : GQp p →* GL (Fin n) k} {S : Set (GQp p)}
    (h : ∀ σ ∈ S, ρ σ = 1) : codimInv ρ S = 0 := by
  rw [codimInv, invariants_eq_top h, finrank_top, Module.finrank_fin_fun, Nat.sub_self]

/-- **Sanity (a1).** If `ρ` is unramified (trivial on `I_p`), `Sw_L(ρ) = 0` at every level. -/
theorem swanAt_eq_zero_of_unramified {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ inertiaSet, ρ σ = 1) (L : Fld p) : swanAt L ρ = 0 := by
  rw [swanAt]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [codimInv_eq_zero (fun σ hσ => h σ (wildSet_subset_inertiaSet hσ.2))]
  simp

/-- **Sanity (a).** Unramified ⇒ conductor exponent `0` (whatever `L` the definition picks). -/
theorem condExp_eq_zero_of_unramified {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ inertiaSet, ρ σ = 1) : condExp ρ = 0 := by
  rw [condExp, codimInv_eq_zero h, swan]
  split_ifs with hL
  · rw [swanAt_eq_zero_of_unramified h]; simp
  · simp

theorem condAt_eq_zero_of_unramified {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ inertiaSet, ρ σ = 1) (L : Fld p) : condAt L ρ = 0 := by
  rw [condAt, codimInv_eq_zero h, swanAt_eq_zero_of_unramified h]; simp

/-- `V^S = V^T` when `S ⊆ T` and every element of `T` agrees on `L` with one of `S`, and `ρ` is
trivial on `G_L`. -/
theorem invariants_eq_of_cover {ρ : GQp p →* GL (Fin n) k} {L : Fld p} {S T : Set (GQp p)}
    (hfix : ∀ σ ∈ fixSet L, ρ σ = 1) (hST : S ⊆ T)
    (hcov : ∀ σ ∈ T, ∃ τ ∈ S, ∀ x ∈ L, τ x = σ x) : invariants ρ S = invariants ρ T := by
  apply le_antisymm
  · intro v hv σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := hcov σ hσ
    have h1 : τ⁻¹ * σ ∈ fixSet L := by
      intro x hx
      change τ⁻¹ (σ x) = x
      rw [← hτσ x hx]
      exact τ.symm_apply_apply x
    have h2 : ρ σ = ρ τ * ρ (τ⁻¹ * σ) := by rw [← map_mul, mul_inv_cancel_left]
    rw [h2, hfix _ h1, mul_one]
    exact hv τ hτ
  · intro v hv σ hσ
    exact hv σ (hST hσ)

/-- **Restriction of inertia is onto** `G_0(L/ℚ_p)` and of wild inertia onto `G_i(L/ℚ_p)`,
`i ≥ 1`, together with `I_p ⊆ ramSet L 0` (Serre, *Corps locaux* I §7 Prop. 21 and IV §1–2;
UNVERIFIED numbering). STANDARD; stated, not proved here. -/
def InertiaRestriction (L : Fld p) : Prop :=
  inertiaSet ⊆ ramSet L 0 ∧
  (∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x) ∧
  (∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x)

/-- `G_i(L/ℚ_p) = 1` for `i ≥ N` (Serre IV §1; holds for every finite `L`). -/
def EventuallyTrivial (L : Fld p) (N : ℕ) : Prop := ∀ i, N ≤ i → ramSet L i ⊆ fixSet L

/-- **Sanity (b). Agreement with the Artin conductor on finite image.** If `ρ` factors through
`Gal(L/ℚ_p)` (trivial on `G_L`), then `codim V^I + Sw_L(ρ)` equals the finite-level Artin
conductor `∑_{i≥0} (g_i/g_0) codim V^{G_i}` (pkg-I6's `artinConductor` formula), given the
restriction facts `InertiaRestriction L`, `G_i(L/ℚ_p) = 1` for large `i`, and `g_0 ≠ 0`. -/
theorem condAt_eq_artinAt {ρ : GQp p →* GL (Fin n) k} {L : Fld p}
    (hfix : ∀ σ ∈ fixSet L, ρ σ = 1) (hR : InertiaRestriction L) {N : ℕ}
    (hN : EventuallyTrivial L N) (hg0 : ramCard L 0 ≠ 0) :
    condAt L ρ = artinAt L ρ := by
  obtain ⟨hI, hIc, hW⟩ := hR
  have e0 : codimInv ρ inertiaSet = codimInv ρ (ramSet L 0) := by
    rw [codimInv, codimInv, invariants_eq_of_cover hfix hI hIc]
  have ei : ∀ i, codimInv ρ (ramSet L (i + 1) ∩ wildSet) = codimInv ρ (ramSet L (i + 1)) := by
    intro i
    rw [codimInv, codimInv, invariants_eq_of_cover hfix Set.inter_subset_left (hW i)]
  have hz : ∀ i, N ≤ i → codimInv ρ (ramSet L i) = 0 := fun i hi =>
    codimInv_eq_zero fun σ hσ => hfix σ (hN i hi hσ)
  set f : ℕ → ℚ := fun i => ((ramCard L i : ℚ) / ramCard L 0) * (codimInv ρ (ramSet L i) : ℚ)
    with hf
  have hsupp : Function.support f ⊆ ↑(Finset.range (N + 1)) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hi (by simp [f, hz i (by omega)])
  have hsupp' : Function.support (fun i => f (i + 1)) ⊆ ↑(Finset.range N) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hi (by simp [f, hz (i + 1) (by omega)])
  have hA : artinAt L ρ = ∑ i ∈ Finset.range (N + 1), f i :=
    finsum_eq_sum_of_support_subset f hsupp
  have hS : swanAt L ρ = ∑ i ∈ Finset.range N, f (i + 1) := by
    rw [swanAt]
    simp_rw [ei]
    exact finsum_eq_sum_of_support_subset (fun i => f (i + 1)) hsupp'
  rw [condAt, hA, hS, Finset.sum_range_succ', e0, add_comm]
  congr 1
  simp only [f]
  rw [div_self (by exact_mod_cast hg0), one_mul]

/-- **Independence of the level** (Serre–Tate 1968 §2; a consequence of Herbrand's theorem,
pkg-I6 leaf I6.8, and the transitivity I6.9). GLUE, not proved here. -/
def SwanIndependent : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L L' : Fld p),
    IsAdapted L ρ → IsAdapted L' ρ → swanAt L ρ = swanAt L' ρ

/-- Under `SwanIndependent`, the conductor exponent is computed at any adapted level. -/
theorem condExp_eq_condAt (hI : SwanIndependent (p := p)) {k : Type} [Field k]
    {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsAdapted L ρ) : condExp ρ = condAt L ρ := by
  have h : ∃ L : Fld p, IsAdapted L ρ := ⟨L, hL⟩
  rw [condExp, condAt, swan, dite_cond_eq_true (eq_true h), hI k n ρ _ L h.choose_spec hL]

/-- **Existence of an adapted level** (Serre–Tate 1968 §2, after Grothendieck: `ρ(P_p)` is finite
for `ℓ ≠ p` since `P_p` is pro-`p` and the kernel of `GL_n(𝓞_E) → GL_n(𝓞_E/λ)` is pro-`ℓ`; a
continuous `ρ` into `GL_n(ℚ̄_ℓ)` takes values in `GL_n(E)`, `E/ℚ_ℓ` finite). GLUE (elementary
profinite group theory plus Baire), not proved here. -/
def AdaptedExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)),
    Continuous ρ → ∃ L : Fld p, IsAdapted L ρ

/-! ## Part D. The leaves -/

/-- **R17 = glue-conductor's L10: Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A)** at `F = ℚ`,
weight 2, pp. 409-411 and §0.8 p. 411 (read by the locator audit: all finite `p` and every
`ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`; the finite discrete-series hypothesis concerns only totally
real `F` of even degree), with `a(π_p) = v_p(N)` for newforms (Casselman 1973, locator
UNVERIFIED). Do not replace it by Théorème (B) or by the `Γ₀` elliptic-curve corollary.
*2026-11-12 (loc-fix, applying rv-loc-leaves (f)):* this replaces "content and coverage of
`p ∣ N` UNVERIFIED"; the Lean statement is unchanged. This form, at every adapted level, is a
consequence of the published form `CarayolR17'` plus the glue `SwanIndependent`
(`carayolR17_of_R17'`); it is not a separate published statement. For a newform `f` of weight 2,
level `N`, and a semisimple `ρ` attached to
`f` (pkg-I4's trace form), and a prime `p ≠ ℓ`, the conductor exponent of `ρ|_{G_{ℚ_p}}` is
`v_p(N)`; stated at every adapted level (equivalent to the published form by `SwanIndependent`). -/
def CarayolR17 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ) [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ →
    ∀ L : Fld p, IsAdapted L (ρ.restrictLocal p) →
      condAt L (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- **R17, published form**, with the canonical `condExp` (choice of level inside): Carayol,
Théorème (A), coverage as above (every `ℓ`, including 2; every `p ≠ ℓ`, including `p ∣ N`; read by
the locator audit, adopted 2026-11-12 by loc-fix). `condExp` is the Serre–Tate conductor, which
does not change under duals, so the Tate normalization of `AttachedTo` is harmless. -/
def CarayolR17' : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ) [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ →
      condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- The two forms of R17 agree given the glue `SwanIndependent` and `AdaptedExists`. -/
theorem carayolR17_of_R17' (hI : ∀ (p : ℕ) [Fact p.Prime], SwanIndependent (p := p))
    (h : CarayolR17') : CarayolR17 := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp L hL
  rw [← condExp_eq_condAt (hI p) hL]
  exact h ℓ ιC ιL N χ f ρ p hN hf hs ha hp

theorem carayolR17'_of_R17 (hE : ∀ (p : ℕ) [Fact p.Prime], AdaptedExists (p := p))
    (hI : ∀ (p : ℕ) [Fact p.Prime], SwanIndependent (p := p))
    (h : CarayolR17) : CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp
  obtain ⟨L, hL⟩ := hE p ℓ hp.symm 2 (ρ.restrictLocal p)
    (ρ.continuous_toHom.comp
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous_toFun)
  rw [condExp_eq_condAt (hI p) hL]
  exact h ℓ ιC ιL N χ f ρ p hN hf hs ha hp L hL

/-- **L8 (glue-conductor): the Swan conductor is the integral of the upper filtration**,
`Sw(ρ) = ∫₀^∞ codim V^{G^u} du` (Serre, *Corps locaux* VI §2 and IV §3 for finite image;
Serre–Tate 1968 §2 for ℓ-adic `ρ`; UNVERIFIED numbering). With `condAt = codim V^I + swanAt`
this is glue-conductor's `a = codim V^I + ∫₀^∞ codim V^{G^u} du`. A change of variables in
Herbrand's `φ` plus Herbrand's theorem: provable glue over Part B. -/
def SwanIntegral : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
    ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)), Continuous ρ →
    ∀ L : Fld p, IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ)

/-! ### Consumer: glue-conductor's D4(i) from L8 (GLUE, proved) -/

theorem codimInv_le (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) : codimInv ρ S ≤ n :=
  Nat.sub_le _ _

open MeasureTheory in
/-- If `ρ` is trivial on `G^u` for every `u > U ≥ 0`, the right side of L8 is `≤ n·U`. (If the
integrand is not integrable, Mathlib's integral is `0` and the bound is trivial.) -/
theorem integral_codim_le (ρ : GQp p →* GL (Fin n) k) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ u : ℝ, U < u → ∀ σ ∈ upperAbs p u, ρ σ = 1) :
    ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ) ≤ n * U := by
  set f : ℝ → ℝ := fun u => (codimInv ρ (upperAbs p u) : ℝ) with hf
  set g : ℝ → ℝ := (Set.Ioc 0 U).indicator (fun _ => (n : ℝ)) with hg
  have hle : ∀ u ∈ Set.Ioi (0 : ℝ), f u ≤ g u := by
    intro u hu
    by_cases huU : u ≤ U
    · have : u ∈ Set.Ioc 0 U := ⟨hu, huU⟩
      simp only [hf, hg, Set.indicator_of_mem this]
      exact_mod_cast codimInv_le ρ _
    · have h0 : codimInv ρ (upperAbs p u) = 0 := codimInv_eq_zero (h u (lt_of_not_ge huU))
      simp only [hf, h0, Nat.cast_zero]
      exact Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg n) u
  have hgi : ∫ u in Set.Ioi (0 : ℝ), g u = n * U := by
    rw [hg, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self, setIntegral_const]
    simp [Real.volume_real_Ioc_of_le hU, mul_comm]
  have hgint : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    rw [IntegrableOn, hg, integrable_indicator_iff measurableSet_Ioc]
    refine IntegrableOn.restrict ?_
    exact integrableOn_const (by simp [Real.volume_Ioc])
  by_cases hfi : IntegrableOn f (Set.Ioi (0 : ℝ))
  · rw [← hgi]
    exact setIntegral_mono_on hfi hgint measurableSet_Ioi hle
  · rw [integral_undef hfi]
    positivity

/-- **D4(i) from L8 (GLUE, proved).** For continuous ℓ-adic `ρ`, `ℓ ≠ p`, trivial on `G^u` for
`u > U ≥ 0`, and `L` adapted: `a(ρ) = codim V^I + Sw_L(ρ) ≤ n(1 + U)`. -/
theorem condAt_le_of_upper (hL8 : SwanIntegral) (ℓ : ℕ) [Fact ℓ.Prime] (hp : p ≠ ℓ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)) (hc : Continuous ρ) (L : Fld p)
    (hL : IsAdapted L ρ) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ u : ℝ, U < u → ∀ σ ∈ upperAbs p u, ρ σ = 1) :
    (condAt L ρ : ℝ) ≤ n * (1 + U) := by
  have h1 : ((codimInv ρ inertiaSet : ℕ) : ℝ) ≤ n := by exact_mod_cast codimInv_le ρ _
  have h2 := integral_codim_le ρ U hU h
  rw [← hL8 ℓ p hp n ρ hc L hL] at h2
  rw [condAt, Rat.cast_add, Rat.cast_natCast]
  linarith

/-! ### Non-degeneracy checks -/

/-- `G_L ⊆ G_i(L)` (preimage) as soon as `L` has a uniformizer. -/
theorem fixSet_subset_ramSet {L : Fld p} {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (i : ℕ) :
    fixSet L ⊆ ramSet L i := by
  intro σ hσ
  refine ⟨ϖ, hϖ, fun x hx _ => ?_⟩
  rw [hσ x hx, sub_self, norm_zero]
  positivity

/-- The trivial representation is adapted to every finite Galois `L`, and has conductor `0`. -/
theorem isAdapted_one {L : Fld p} (hL : IsFinGal L) :
    IsAdapted L (1 : GQp p →* GL (Fin n) k) :=
  ⟨hL, fun _ _ => rfl⟩

theorem condExp_one : condExp (1 : GQp p →* GL (Fin n) k) = 0 :=
  condExp_eq_zero_of_unramified fun _ _ => rfl

/-- Wild inertia contains `1`. -/
theorem one_mem_wildSet : (1 : GQp p) ∈ wildSet := by
  intro x hx
  simp only [AlgEquiv.one_apply, sub_self, norm_zero]
  exact norm_pos_iff.mpr hx

/-- Galois conjugates of elements of a finite Galois `L ⊆ ℚ̄_p` lie in `L`. -/
theorem apply_mem {L : Fld p} (hL : IsFinGal L) (σ : GQp p) {x : Kbar p} (hx : x ∈ L) :
    σ x ∈ L := by
  have : IsGalois ℚ_[p] L := hL.2
  have hn : Normal ℚ_[p] L := inferInstance
  exact (IntermediateField.normal_iff_forall_map_le'.1 hn σ) ⟨x, hx, rfl⟩

/-- **First clause of `InertiaRestriction` (proved):** `I_p ⊆ ramSet L 0` for finite Galois `L`
with a uniformizer. -/
theorem inertiaSet_subset_ramSet_zero {L : Fld p} (hL : IsFinGal L) {ϖ : Kbar p}
    (hϖ : IsUnif L ϖ) : inertiaSet ⊆ ramSet L 0 := by
  intro σ hσ
  refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
  rw [zero_add, pow_one]
  exact hϖ.2.2 _ (L.sub_mem (apply_mem hL σ hx) hx) (hσ x hx1)

theorem norm_p_kbar : ‖(p : Kbar p)‖ = (p : ℝ)⁻¹ := by
  have h := PadicAlgCl.norm_extends p (p : ℚ_[p])
  have e : ((p : ℚ_[p]) : PadicAlgCl p) = (p : Kbar p) := map_natCast (algebraMap ℚ_[p] _) p
  rw [e, Padic.norm_p] at h
  exact h

/-- **Non-vacuity of `IsUnif`:** `p` is a uniformizer of `L = ℚ_p`. -/
theorem isUnif_bot : IsUnif (⊥ : Fld p) (p : Kbar p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  · rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
  · intro y hy hy1
    obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.1 hy
    have hq : ‖algebraMap ℚ_[p] (Kbar p) q‖ = ‖q‖ := PadicAlgCl.norm_extends p q
    rw [hq] at hy1 ⊢
    rw [norm_p_kbar]
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one q (-1)).2 (by simpa using hy1)
    simpa [zpow_neg_one] using this

/-- The restrictions to a finite `L` of elements of `G_{ℚ_p}` form a finite set. -/
theorem finite_restr {L : Fld p} (hL : IsFinGal L) (S : Set (GQp p)) :
    (restr L '' S).Finite := by
  have : FiniteDimensional ℚ_[p] L := hL.1
  refine (Set.finite_range (fun f : L →ₐ[ℚ_[p]] Kbar p => (f : L → Kbar p))).subset ?_
  rintro _ ⟨σ, -, rfl⟩
  exact ⟨σ.toAlgHom.comp L.val, rfl⟩

/-- **`g_0 ≠ 0` (proved)** for a finite Galois `L` with a uniformizer. -/
theorem ramCard_ne_zero {L : Fld p} (hL : IsFinGal L) {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (i : ℕ) :
    ramCard L i ≠ 0 := by
  have hne : (restr L '' ramSet L i).Nonempty :=
    ⟨restr L 1, 1, fixSet_subset_ramSet hϖ i (fun x _ => rfl), rfl⟩
  have hfin := finite_restr hL (ramSet L i)
  have : Finite (restr L '' ramSet L i) := hfin.to_subtype
  have : Nonempty (restr L '' ramSet L i) := hne.to_subtype
  exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩

/-- **Sanity (b), reduced hypotheses.** For `L` finite Galois with a uniformizer and `ρ` trivial on
`G_L`: `codim V^I + Sw_L = ∑_{i≥0}(g_i/g_0) codim V^{G_i}`, assuming only the two surjectivity
statements (restriction of `I_p` onto `G_0(L)`, of `P_p ∩ G_i` onto `G_i(L)` for `i ≥ 1`) and
`G_i(L) = 1` for `i ≥ N`. -/
theorem condAt_eq_artinAt' {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsFinGal L)
    {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (hfix : ∀ σ ∈ fixSet L, ρ σ = 1)
    (hI : ∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x)
    (hW : ∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x)
    {N : ℕ} (hN : EventuallyTrivial L N) :
    condAt L ρ = artinAt L ρ :=
  condAt_eq_artinAt hfix ⟨inertiaSet_subset_ramSet_zero hL hϖ, hI, hW⟩ hN
    (ramCard_ne_zero hL hϖ 0)

/-- Two uniformizers of `L` have the same absolute value. -/
theorem IsUnif.norm_eq {L : Fld p} {ϖ ϖ' : Kbar p} (h : IsUnif L ϖ) (h' : IsUnif L ϖ') :
    ‖ϖ'‖ = ‖ϖ‖ :=
  le_antisymm (h.2.2 _ h'.1 h'.2.1) (h'.2.2 _ h.1 h.2.1)

/-- If `σ₀` moves `L`, then for large `i` no element of `ramSet L i` restricts to `σ₀|_L`. -/
theorem eventually_not_restr {L : Fld p} {ϖ : Kbar p} (hϖ : IsUnif L ϖ) {σ₀ : GQp p}
    (h₀ : σ₀ ∉ fixSet L) :
    ∃ N : ℕ, ∀ i, N ≤ i → ∀ σ ∈ ramSet L i, restr L σ ≠ restr L σ₀ := by
  simp only [fixSet, Set.mem_setOf_eq, not_forall] at h₀
  obtain ⟨y, hy, hσy⟩ := h₀
  have hpn : ‖(p : Kbar p)‖ < 1 := by
    rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖y‖ + 1) by positivity) hpn
  set x₀ : Kbar p := (p : Kbar p) ^ k * y with hx₀
  have hpk : (p : Kbar p) ^ k = algebraMap ℚ_[p] (Kbar p) ((p : ℚ_[p]) ^ k) := by simp
  have hx₀L : x₀ ∈ L := L.mul_mem (hpk ▸ IntermediateField.algebraMap_mem _ _) hy
  have hx₀1 : ‖x₀‖ ≤ 1 := by
    rw [hx₀, norm_mul, norm_pow]
    have h1 : ‖(p : Kbar p)‖ ^ k * (‖y‖ + 1) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hk
    nlinarith [norm_nonneg y, pow_nonneg (norm_nonneg (p : Kbar p)) k]
  have hσx₀ : σ₀ x₀ - x₀ = (p : Kbar p) ^ k * (σ₀ y - y) := by
    rw [hx₀, map_mul, map_pow, map_natCast]; ring
  have hε : 0 < ‖σ₀ x₀ - x₀‖ := by
    rw [hσx₀, norm_pos_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
      (sub_ne_zero.2 hσy)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hϖ.2.1
  refine ⟨N, fun i hi σ hσ heq => ?_⟩
  obtain ⟨ϖ', hϖ', hb⟩ := hσ
  have e : σ x₀ = σ₀ x₀ := congrFun heq ⟨x₀, hx₀L⟩
  have h1 := hb x₀ hx₀L hx₀1
  rw [e, hϖ.norm_eq hϖ'] at h1
  have h2 : ‖ϖ‖ ^ (i + 1) ≤ ‖ϖ‖ ^ N :=
    pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)
  linarith

/-- **`G_i(L/ℚ_p) = 1` for large `i` (proved)**, for finite Galois `L` with a uniformizer. -/
theorem eventuallyTrivial {L : Fld p} (hL : IsFinGal L) {ϖ : Kbar p} (hϖ : IsUnif L ϖ) :
    ∃ N, EventuallyTrivial L N := by
  have key : ∀ T : Set (L → Kbar p), T.Finite → T ⊆ restr L '' (fixSet L)ᶜ →
      ∃ N : ℕ, ∀ i, N ≤ i → ∀ σ ∈ ramSet L i, restr L σ ∉ T := by
    intro T hT
    induction T, hT using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨0, fun _ _ _ _ h => h⟩
    | @insert f T' _ _ ih =>
      intro hsub
      obtain ⟨N₁, hN₁⟩ := ih (fun g hg => hsub (Set.mem_insert_of_mem _ hg))
      obtain ⟨σ₀, h₀, rfl⟩ := hsub (Set.mem_insert _ _)
      obtain ⟨N₀, hN₀⟩ := eventually_not_restr hϖ h₀
      refine ⟨max N₀ N₁, fun i hi σ hσ hmem => ?_⟩
      rcases hmem with h | h
      · exact hN₀ i (le_of_max_le_left hi) σ hσ h
      · exact hN₁ i (le_of_max_le_right hi) σ hσ h
  obtain ⟨N, hN⟩ := key _ (finite_restr hL _) le_rfl
  refine ⟨N, fun i hi σ hσ => ?_⟩
  by_contra hfix
  exact hN i hi σ hσ ⟨σ, hfix, rfl⟩

/-- **Sanity (b), final form.** For `L` finite Galois with a uniformizer and `ρ` trivial on `G_L`,
`codim V^I + Sw_L = ∑_{i≥0}(g_i/g_0) codim V^{G_i}`, given only the two surjectivity facts. -/
theorem condAt_eq_artinAt'' {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsFinGal L)
    {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (hfix : ∀ σ ∈ fixSet L, ρ σ = 1)
    (hI : ∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x)
    (hW : ∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x) :
    condAt L ρ = artinAt L ρ :=
  let ⟨_, hN⟩ := eventuallyTrivial hL hϖ
  condAt_eq_artinAt' hL hϖ hfix hI hW hN

/-- For `y ≠ 0` in a finite `L/ℚ_p`, `‖y‖^{[L:ℚ_p]!}` is an integral power of `p` (from Mathlib's
`spectralNorm_eq_norm_coeff_zero_rpow`: `‖y‖ = ‖a_0‖^{1/deg}` for the minimal polynomial). -/
theorem norm_pow_factorial {L : Fld p} (hL : FiniteDimensional ℚ_[p] L) {y : Kbar p}
    (hy : y ∈ L) (hy0 : y ≠ 0) :
    ∃ j : ℤ, ‖y‖ ^ (Module.finrank ℚ_[p] L).factorial = (p : ℝ) ^ j := by
  have hint : IsIntegral ℚ_[p] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  set m := (minpoly ℚ_[p] y).natDegree with hm
  have hm_le : m ≤ Module.finrank ℚ_[p] L := by
    have := minpoly.natDegree_le (A := ℚ_[p]) (⟨y, hy⟩ : L)
    rwa [IntermediateField.minpoly_eq] at this
  have hm_pos : 0 < m := minpoly.natDegree_pos hint
  obtain ⟨t, ht⟩ := Nat.dvd_factorial hm_pos hm_le
  set c := (minpoly ℚ_[p] y).coeff 0 with hc
  have hc0 : c ≠ 0 := minpoly.coeff_zero_ne_zero hint hy0
  have hnorm : ‖y‖ = ‖c‖ ^ (1 / m : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := Kbar p) y
  have hym : ‖y‖ ^ m = ‖c‖ := by
    rw [hnorm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have : (1 / (m : ℝ)) * (m : ℝ) = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  refine ⟨-c.valuation * t, ?_⟩
  rw [ht, pow_mul, hym, Padic.norm_eq_zpow_neg_valuation hc0, ← zpow_natCast, ← zpow_mul]

/-- **Every finite `L/ℚ_p` inside `ℚ̄_p` has a uniformizer (proved).** -/
theorem exists_isUnif {L : Fld p} (hL : FiniteDimensional ℚ_[p] L) : ∃ ϖ, IsUnif L ϖ := by
  classical
  set D := (Module.finrank ℚ_[p] L).factorial with hDdef
  have hD : 0 < D := Nat.factorial_pos _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpL : (p : Kbar p) ∈ L := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hex : ∃ n : ℕ, ∃ y ∈ L, ‖y‖ < 1 ∧ ‖y‖ ^ D = (p : ℝ) ^ (-(n : ℤ)) :=
    ⟨D, p, hpL, isUnif_bot.2.1, by rw [norm_p_kbar, zpow_neg, zpow_natCast, inv_pow]⟩
  obtain ⟨ϖ, hϖL, hϖ1, hϖD⟩ := Nat.find_spec hex
  refine ⟨ϖ, hϖL, hϖ1, fun y hy hy1 => ?_⟩
  by_cases hy0 : y = 0
  · rw [hy0, norm_zero]; exact norm_nonneg _
  obtain ⟨j, hj⟩ := norm_pow_factorial hL hy hy0
  have hjneg : j < 0 := by
    have h1 : ‖y‖ ^ D < 1 := pow_lt_one₀ (norm_nonneg _) hy1 hD.ne'
    rw [hj] at h1
    by_contra h
    rw [not_lt] at h
    exact absurd h1 (not_lt.2 (one_le_zpow₀ hp1.le h))
  have hle : Nat.find hex ≤ (-j).toNat :=
    Nat.find_min' hex ⟨y, hy, hy1, by rw [hj]; congr 1; omega⟩
  have hDle : ‖y‖ ^ D ≤ ‖ϖ‖ ^ D := by
    rw [hj, hϖD]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hD.ne').1 hDle

/-- **Sanity (b), with no structural hypotheses.** For `L/ℚ_p` finite Galois and `ρ` trivial on
`G_L`: `codim V^I + Sw_L = ∑_{i≥0}(g_i/g_0) codim V^{G_i}`, given the two surjectivity facts. -/
theorem condAt_eq_artinAt_of_surj {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsFinGal L)
    (hfix : ∀ σ ∈ fixSet L, ρ σ = 1)
    (hI : ∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x)
    (hW : ∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x) :
    condAt L ρ = artinAt L ρ :=
  let ⟨_, hϖ⟩ := exists_isUnif hL.1
  condAt_eq_artinAt'' hL hϖ hfix hI hW

end LadicCond
end
end LadicCondSec

/-! ## Kernel copy: ZInQKernel/HDecomp/Descent/WP3.lean (verbatim minus imports). Needed by g0-mod-field (T14/T15 → LeafHasse/LeafLocalTwo). -/
section GlueWP3Sec

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-wp3/WP3.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-wp3: glue-descent's `LeafHasse`, `LeafLocalTwo` from the announced leaves T14-T15

The leaf bundle (`scratch/h-decomposition/Leaves.lean`, `HSyn` bundle fields `t14a`, `t14b`,
`t15`) announces the Brauer facts as pkg-I6's cochain forms I6.2a′-c′
(`PkgI6.BrauerHasse2C`, `PkgI6.BrauerReciprocity2C`, `PkgI6.LocalH2CardC`: continuous
inhomogeneous cochains `G × G → ZMod 2`, all places including `∞`).  glue-descent proved B2-B3
(`GlueDescent.B3Q.b3_degree_le_QM`) from its own forms `GlueDescent.B2Q.LeafHasse`,
`LeafLocalTwo` (locally constant `ℂˣ`-valued cochains with square `1`, finite places only).

This file proves (no sorry; axioms propext, Classical.choice, Quot.sound):

* `leafHasse_of_T14 : BrauerHasse2C → BrauerReciprocity2C → LeafHasse`
* `leafLocalTwo_of_T15 : LocalH2CardC → LeafLocalTwo`
* `b3_degree_le_QM_of_T14_T15`: glue-descent's B2-B3 theorem with `LeafHasse`, `LeafLocalTwo`
  replaced by the announced T14-T15.

The glue is (i) the dictionary `±1 ⊂ ℂˣ` ↔ `ZMod 2` (`sgn`, `unsgn`) between the two cochain
languages, compatible with cocycles, coboundaries and restriction along `G_{ℚ_p} → G_ℚ` (both
sides use the same Mathlib map `Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])`), and
(ii) the real place: a class trivial at every finite prime is trivial at `∞` by reciprocity
(the parity of the number of ramified places).

In the draft, the definitions of `PkgI6` and glue-descent's files were verbatim copies; here
they are imported from `Conductor/I6Base.lean` and `Descent/*.lean`.
-/

/-! The `PkgI6` cochain definitions and leaves are imported from
`ZInQKernel.HDecomp.Conductor.I6Base`. -/

noncomputable section

namespace GlueWP3

open GlueDescent.B2 GlueDescent.B2Q PkgI6

/-! ## The dictionary `ZMod 2` ↔ `±1 ⊂ ℂˣ` -/

/-- `ZMod 2 → ±1 ⊂ ℂˣ`, `0 ↦ 1`, `1 ↦ -1`. -/
def sgn (a : ZMod 2) : ℂˣ := if a = 0 then 1 else -1

/-- `±1 → ZMod 2`, `1 ↦ 0`, anything else `↦ 1`. -/
def unsgn (s : ℂˣ) : ZMod 2 := if s = 1 then 0 else 1

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_one : sgn 1 = -1 := by simp [sgn]

theorem neg_one_ne_one : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at this

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [sgn]
  · simp [sgn]
  · simp [sgn]
  · have : (1 + 1 : ZMod 2) = 0 := by decide
    rw [this, sgn_zero, sgn_one]; simp

theorem sgn_neg (a : ZMod 2) : sgn (-a) = sgn a := by
  rcases zmod2_cases a with rfl | rfl
  · simp
  · have : (-1 : ZMod 2) = 1 := by decide
    rw [this]

theorem sgn_sub (a b : ZMod 2) : sgn (a - b) = sgn a * sgn b := by
  rw [sub_eq_add_neg, sgn_add, sgn_neg]

theorem sgn_sq (a : ZMod 2) : sgn a ^ 2 = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp [sgn]

theorem sgn_inv (a : ZMod 2) : (sgn a)⁻¹ = sgn a := by
  rw [inv_eq_iff_mul_eq_one, ← sq, sgn_sq]

theorem sgn_injective : Function.Injective sgn := by
  intro a b h
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rfl
  · rw [sgn_zero, sgn_one] at h; exact absurd h.symm neg_one_ne_one
  · rw [sgn_zero, sgn_one] at h; exact absurd h neg_one_ne_one
  · rfl

theorem sgn_eq_one_iff (a : ZMod 2) : sgn a = 1 ↔ a = 0 := by
  rw [← sgn_zero]; exact sgn_injective.eq_iff

/-- A unit of `ℂ` with square `1` is `±1`. -/
theorem sq_eq_one_cases {s : ℂˣ} (h : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have h' : (s : ℂ) * s = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simpa [sq] using this
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · left; exact Units.ext h1
  · right; exact Units.ext (by simpa using h1)

theorem sgn_unsgn {s : ℂˣ} (h : s ^ 2 = 1) : sgn (unsgn s) = s := by
  rcases sq_eq_one_cases h with rfl | rfl
  · simp [unsgn, sgn]
  · simp [unsgn, sgn]

/-! ## Cocycles and coboundaries correspond -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Push a `ZMod 2` cochain to a sign cochain. -/
def sgnC (ε : G → G → ZMod 2) : G → G → ℂˣ := fun x y => sgn (ε x y)

/-- Pull a sign cochain back to a `ZMod 2` cochain. -/
def unsgnC (η : G → G → ℂˣ) : G → G → ZMod 2 := fun x y => unsgn (η x y)

theorem sgnC_unsgnC {η : G → G → ℂˣ} (h : ∀ x y, η x y ^ 2 = 1) : sgnC (unsgnC η) = η := by
  funext x y; exact sgn_unsgn (h x y)

theorem isCocycle2_iff (ε : G → G → ZMod 2) : IsCocycle2 ε ↔ IsSignCocycle (sgnC ε) := by
  constructor
  · rintro ⟨hc, hcoc⟩
    refine ⟨?_, fun x y => sgn_sq _, fun x y z => ?_⟩
    · have : IsLocallyConstant (fun x : G × G => ε x.1 x.2) :=
        (IsLocallyConstant.iff_continuous _).mpr hc
      exact this.comp sgn
    · -- `ε y z - ε (xy) z + ε x (yz) - ε x y = 0`
      have h := congrArg sgn (hcoc x y z)
      rw [sgn_sub, sgn_add, sgn_sub, sgn_zero] at h
      simp only [sgnC]
      have e1 := sgn_inv (ε (x * y) z)
      have e2 := sgn_inv (ε x y)
      calc sgn (ε (x * y) z) * sgn (ε x y)
          = sgn (ε (x * y) z) * sgn (ε x y) *
            (sgn (ε y z) * sgn (ε (x * y) z) * sgn (ε x (y * z)) * sgn (ε x y)) := by
            rw [h, mul_one]
        _ = sgn (ε y z) * sgn (ε x (y * z)) *
            ((sgn (ε (x * y) z) * sgn (ε (x * y) z)) * (sgn (ε x y) * sgn (ε x y))) := by ac_rfl
        _ = sgn (ε y z) * sgn (ε x (y * z)) := by
            rw [← sq, ← sq, sgn_sq, sgn_sq, one_mul, mul_one]
  · rintro ⟨hl, -, hcoc⟩
    refine ⟨?_, fun a b c => ?_⟩
    · have hl' : IsLocallyConstant (fun x : G × G => ε x.1 x.2) := by
        have := hl.comp unsgn
        have e : (unsgn ∘ Function.uncurry (sgnC ε)) = fun x : G × G => ε x.1 x.2 := by
          funext ⟨x, y⟩
          show unsgn (sgn (ε x y)) = ε x y
          rcases zmod2_cases (ε x y) with h | h <;> rw [h] <;> simp [sgn, unsgn]
        rwa [e] at this
      exact hl'.continuous
    · apply sgn_injective
      rw [sgn_sub, sgn_add, sgn_sub, sgn_zero]
      have h := hcoc a b c
      simp only [sgnC] at h
      calc sgn (ε b c) * sgn (ε (a * b) c) * sgn (ε a (b * c)) * sgn (ε a b)
          = (sgn (ε b c) * sgn (ε a (b * c))) * (sgn (ε (a * b) c) * sgn (ε a b)) := by ac_rfl
        _ = (sgn (ε (a * b) c) * sgn (ε a b)) * (sgn (ε (a * b) c) * sgn (ε a b)) := by rw [h]
        _ = 1 := by rw [← sq, mul_pow, sgn_sq, sgn_sq, mul_one]

theorem isCoboundary2_iff (ε : G → G → ZMod 2) : IsCoboundary2 ε ↔ SignCob (sgnC ε) := by
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨fun x => sgn (f x), ((IsLocallyConstant.iff_continuous f).mpr hf).comp sgn,
      fun x => sgn_sq _, fun x y => ?_⟩
    simp only [sgnC, dB, he, sgn_add, sgn_sub, sgn_inv]
    ac_rfl
  · rintro ⟨γ, hγl, hγs, he⟩
    refine ⟨fun x => unsgn (γ x), (hγl.comp unsgn).continuous, fun a b => ?_⟩
    apply sgn_injective
    have h := he a b
    simp only [sgnC, dB] at h
    have hi : (γ (a * b))⁻¹ = γ (a * b) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hγs])
    rw [h, sgn_add, sgn_sub, sgn_unsgn (hγs a), sgn_unsgn (hγs b), sgn_unsgn (hγs (a * b)), hi]
    ac_rfl

/-- Every sign cocycle is `sgnC` of a `ZMod 2` cocycle. -/
theorem exists_of_isSignCocycle {η : G → G → ℂˣ} (h : IsSignCocycle η) :
    ∃ ε : G → G → ZMod 2, IsCocycle2 ε ∧ η = sgnC ε :=
  ⟨unsgnC η, by rw [isCocycle2_iff, sgnC_unsgnC h.2.1]; exact h, (sgnC_unsgnC h.2.1).symm⟩

end Generic

/-- Restriction commutes with the dictionary: glue-descent's `pull (resp p)` is pkg-I6's
`resC ℚ_[p]` (the same Mathlib map). -/
theorem pull_resp_sgnC (p : Nat.Primes) (ε : GQ → GQ → ZMod 2) :
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    pull (resp p) (sgnC ε) = sgnC (resC ℚ_[(p : ℕ)] ε) := rfl

/-! ## The two leaves -/

/-- The real place from reciprocity: a `ZMod 2` cocycle of `G_ℚ` that is a coboundary at every
finite prime is a coboundary at `∞` (the number of places where it is locally nontrivial is
even, and there are none at finite primes). -/
theorem real_of_finite (hR : BrauerReciprocity2C) (ε : GQ → GQ → ZMod 2) (hε : IsCocycle2 ε)
    (hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε)) :
    IsCoboundary2 (resC ℝ ε) := by
  classical
  obtain ⟨-, hev⟩ := hR ε hε
  have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
      ¬ IsCoboundary2 (resC ℚ_[(q : ℕ)] ε)} = ∅ := by
    ext q
    have : Fact (q : ℕ).Prime := ⟨q.2⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hp q
  rw [hempty, Set.ncard_empty, zero_add] at hev
  by_contra hne
  rw [if_neg hne] at hev
  exact Nat.not_even_one hev

/-- **glue-descent's `LeafHasse` from T14** (`BrauerHasse2C` and `BrauerReciprocity2C`). -/
theorem leafHasse_of_T14 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C) : LeafHasse := by
  intro η hη hloc
  obtain ⟨ε, hε, rfl⟩ := exists_of_isSignCocycle hη
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε) := by
    intro p hpp
    rw [isCoboundary2_iff]
    exact hloc ⟨p, hpp.out⟩
  rw [← isCoboundary2_iff]
  exact hH ε hε (real_of_finite hR ε hε hp) hp

/-- **glue-descent's `LeafLocalTwo` from T15** (`LocalH2CardC`, its finite-place half; the
existence of a nontrivial class and the real place are not used). -/
theorem leafLocalTwo_of_T15 (hC : LocalH2CardC) : LeafLocalTwo := by
  intro p η₁ η₂ h₁ h₂ hn₁ hn₂
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨ε₁, hε₁, rfl⟩ := exists_of_isSignCocycle h₁
  obtain ⟨ε₂, hε₂, rfl⟩ := exists_of_isSignCocycle h₂
  rw [← isCoboundary2_iff] at hn₁ hn₂
  have h := (hC.1 p).2 ε₁ ε₂ hε₁ hε₂ hn₁ hn₂
  rw [isCoboundary2_iff] at h
  have e : (fun x y => sgnC ε₁ x y * (sgnC ε₂ x y)⁻¹) = sgnC (ε₁ - ε₂) := by
    funext x y
    simp only [sgnC, Pi.sub_apply, sgn_sub, sgn_inv]
  rw [e]
  exact h

/-! ## Converses: glue-descent's forms say no more than the announced leaves -/

/-- `LeafHasse` (finite places only) implies `BrauerHasse2C` outright. -/
theorem brauerHasse2C_of_leafHasse (h : LeafHasse) : BrauerHasse2C := by
  intro ε hε _ hp
  rw [isCoboundary2_iff]
  rw [isCocycle2_iff] at hε
  refine h _ hε fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [pull_resp_sgnC, ← isCoboundary2_iff]
  exact hp p

/-- Given reciprocity, `LeafHasse ↔ BrauerHasse2C`. -/
theorem leafHasse_iff (hR : BrauerReciprocity2C) : LeafHasse ↔ BrauerHasse2C :=
  ⟨brauerHasse2C_of_leafHasse, fun hH => leafHasse_of_T14 hH hR⟩

/-- `LeafLocalTwo` is exactly the second half of `H2TwoClasses (G_{ℚ_p})` for every `p`. -/
theorem leafLocalTwo_iff : LeafLocalTwo ↔ ∀ (p : ℕ) [Fact p.Prime],
    ∀ ε₁ ε₂, IsCocycle2 (G := Field.absoluteGaloisGroup ℚ_[p]) ε₁ → IsCocycle2 ε₂ →
      ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ → IsCoboundary2 (ε₁ - ε₂) := by
  have e : ∀ {G : Type} [Group G] [TopologicalSpace G] (ε₁ ε₂ : G → G → ZMod 2),
      (fun x y => sgnC ε₁ x y * (sgnC ε₂ x y)⁻¹) = sgnC (ε₁ - ε₂) := by
    intro G _ _ ε₁ ε₂
    funext x y
    simp only [sgnC, Pi.sub_apply, sgn_sub, sgn_inv]
  constructor
  · intro h p hp ε₁ ε₂ h₁ h₂ hn₁ hn₂
    rw [isCocycle2_iff] at h₁ h₂
    rw [isCoboundary2_iff] at hn₁ hn₂ ⊢
    rw [← e]
    exact h ⟨p, hp.out⟩ _ _ h₁ h₂ hn₁ hn₂
  · intro h p η₁ η₂ h₁ h₂ hn₁ hn₂
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    obtain ⟨ε₁, hε₁, rfl⟩ := exists_of_isSignCocycle h₁
    obtain ⟨ε₂, hε₂, rfl⟩ := exists_of_isSignCocycle h₂
    rw [← isCoboundary2_iff] at hn₁ hn₂
    rw [e, ← isCoboundary2_iff]
    exact h p ε₁ ε₂ hε₁ hε₂ hn₁ hn₂

/-! ## B2-B3 from the announced leaves -/

/-- **B2-B3 with the constants from the announced leaves**: glue-descent's
`GlueDescent.B3Q.b3_degree_le_QM` with `LeafHasse`, `LeafLocalTwo` replaced by T14-T15
(`BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`).  The remaining hypotheses
`LeafSqrtCrit` (L-B2c, T16) and `LeafUnramified` (L-B2d) are glue-descent's other leaves. -/
theorem b3_degree_le_QM_of_T14_T15 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C)
    (hC : LocalH2CardC) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ GlueDescent.ramSet S u → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GlueDescent.B3Q.GQL L' ↔ σ ∈ GlueDescent.B3Q.GQL L ∧ β σ = 1) ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u :=
  GlueDescent.B3Q.b3_degree_le_QM (leafHasse_of_T14 hH hR) (leafLocalTwo_of_T15 hC) hSq hUnr
    S hS R hRD hRS hR12 u L hLD ε hε hinf h11 hram η hη hηl

end GlueWP3

end

end GlueWP3Sec

section G0ModFieldSec

/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- `T = S_mul ∪ supp M_{S_mul}(u)`, the ramification set (N5 L528). -/
noncomputable def T (u : ℚ) : Finset ℕ := GlueDescent.ramSet Mult.S_mul u

/-- `A`, an abelian variety over the subfield `L ⊆ ℚ̄`, is a model of the surface of the
`ℚ̄`-object `P`: `A_{ℚ̄} ≅ P.A` as `ℚ̄`-schemes (base change along the inclusion `L ⊆ ℚ̄`). -/
def IsModelOver (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  Nonempty ((A.baseChange Qbar).X ≅ P.A.X)

/-- The algebra `L → L'` for `L ≤ L'`. -/
@[instance_reducible] noncomputable def incAlg {L L' : IF} (h : L ≤ L') : Algebra L L' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- **`A/L` is a QM model of `P`**: the base change to `L` of the abelian surface of an object
`PK` of `Y₃`'s moduli problem (QM by `𝒪` with level-3 structure) over a subfield `K ≤ L`, itself a
model of `P`'s surface. Such an `A` has good reduction away from `3` (G3,
`LeafQM.AV.QML3.goodReduction`), unlike an arbitrary model (a twist by a cocycle ramified at
`p ∉ T` has bad reduction at `p`), so the later steps (G11, G15) hold for every such `A`. -/
def IsQMModel (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (hKL : K ≤ L) (PK : QML3 K), IsModelOver K PK.A P ∧
    A = @PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)

/-- **The fibre context** (the hypotheses of `ModularConstituent`): moduli data `(Y, Φ, π)` with
R1-R2's clauses, `u ∉ 𝒞`, and a `ℚ̄`-point `y` of `Y₃` carrying the object `P` and lying over
`J(u)`. -/
def FibreCtx (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) : Prop :=
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ u ∉ contactSet ∧
  ∃ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u))

/-- **A rational fibre over `K`** (Glazer N5 L528: "Choose a fiber `A/K`"): `PK` is an object of
`Y₃` over `K ⊆ ℚ̄` at a `K`-point `yK` whose base change to `ℚ̄` carries `P` (so `yK` lies over the
`ℚ̄`-point of `P`, `Φ` being a bijection), and `PK.A` is a model of `P`'s surface. Unlike an
arbitrary `K`-model (a twist of `PK.A` by a cocycle ramified outside `T` can have bad
reduction there), `PK.A` is the fibre of the universal family and has good reduction away
from `3` (G3). -/
def RationalFibre (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (P : QML3 Qbar) (K : IF)
    (PK : QML3 K) : Prop :=
  (∃ yK : fieldPt K ⟶ Y, Φ K yK = M3.mk PK ∧ Φ Qbar (fieldMap K.val ≫ yK) = M3.mk P) ∧
    IsModelOver K PK.A P

/-! ## The outputs of G2, G4, G7 -/

/-- **G2's output (Lemma PR(i), N5 L524-529).** A finite Galois `K ⊆ ℚ̄` with `[K:ℚ] ≤ F₀ = 324!`,
unramified outside `T`, with a rational fibre `PK/K` over `P` (Glazer: "Choose a fiber `A/K`";
`RationalFibre`). -/
def G2Out (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (_ : FiniteDimensional ℚ K) (_ : IsGalois ℚ K),
    Module.finrank ℚ K ≤ heightF0 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) ∧
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK

/-- `A(ℚ̄)` as an additive group, for `A` over `L ⊆ ℚ̄`. -/
abbrev PtQ (L : IF) (A : PkgI3.AbVar L) : Type := Additive (A.Pt Qbar)

/-- **The descent datum of B1 on the actual `A` (N5 L632-663).** `ε` is a normalized
locally constant sign 2-cocycle of `G_ℚ` inflated from `Gal(L/ℚ)`, and it is the cocycle of `A`:
there are maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` (`μ_σ : ^σA → A` the `B`-linear conjugacy isogeny over
`L`, `σ` acting on coordinates) and reals `a_σ > 0` (`a_σ = (deg μ_σ)^{-1/4}`) with
* `a` inflated from `Gal(L/ℚ)` with `a = 1` on `G_L`,
* `m_σ` the Galois action of `σ` for `σ ∈ G_L` (`μ_σ = 1` there),
* `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L` (`μ` inflated from `Gal(L/ℚ)`, defined
  over `L`),
* `m_σ` commutes with every `L`-endomorphism of `A` (`μ_σ` is `B`-linear and `L` is the Hom
  field),
* `m_σ` surjective with finite kernel (an isogeny composed with a bijection),
* `m_σ m_τ = c(σ,τ) m_{στ}` with `c = n/d ∈ ℚ^×` (the discrepancy commutes with `B`), and
  `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` (N5 L651-660: `ν = aμ`, `ν_σ ^σν_τ = ε ν_{στ}`).
* `m_σ` is algebraic: it is induced by a finite surjective morphism of schemes
  `F_σ : A → A` (`μ_σ`, composed with the identification of the underlying schemes of `^σA` and
  `A`): `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` (G14's trace identities reduce `F_σ` modulo primes).
The maps `m_σ` are on points, hence independent of `ℓ`; on `V_ℓ(A)` they give G8's
`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` (N5 L725-727). -/
def DescentDatum (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) : Prop :=
  IsSignCocycle ε ∧ InflatedFrom L ε ∧ ε 1 1 = 1 ∧
  ∃ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ),
    (∀ σ, 0 < a σ) ∧
    (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) ∧
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
    (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
    (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
    (∀ σ τ, ∃ n d : ℤ, n ≠ 0 ∧ d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ) ∧
        (((a σ * a τ * ((n : ℝ) / d) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) ∧
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ)

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-- The sign of a rational, as `±1 ∈ ℂ^×` (`1` for `q > 0`). -/
noncomputable def sgnU (q : ℚ) : ℂˣ := if 0 < q then 1 else -1

theorem sgnU_sq (q : ℚ) : sgnU q ^ 2 = 1 := by
  unfold sgnU; split_ifs <;> simp

theorem sgnU_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : sgnU (q * r) = sgnU q * sgnU r := by
  unfold sgnU
  rcases lt_or_gt_of_ne hq with hq' | hq' <;> rcases lt_or_gt_of_ne hr with hr' | hr'
  · rw [if_pos (mul_pos_of_neg_of_neg hq' hr'), if_neg (not_lt.2 hq'.le),
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_neg_of_pos hq' hr').le), if_neg (not_lt.2 hq'.le),
      if_pos hr']; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_pos_of_neg hq' hr').le), if_pos hq',
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_pos (mul_pos hq' hr'), if_pos hq', if_pos hr']; simp

/-- `sgn(q)·|q| = q`, in `ℂ`. -/
theorem sgnU_mul_abs (q : ℚ) : ((sgnU q : ℂˣ) : ℂ) * ((|(q : ℝ)| : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by
  unfold sgnU
  split_ifs with h
  · have : (0 : ℝ) < q := by exact_mod_cast h
    rw [abs_of_pos this]; simp
  · have : (q : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 h
    rw [abs_of_nonpos this]; push_cast; ring

/-- **The conjugacy isogenies before normalization (N5 L632-645; the content of G4 + B1's
geometric half).** Maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the first four clauses of
`DescentDatum`; the discrepancy `c(σ,τ) = n/d ∈ ℚ^×` with `d·m_σ m_τ = n·m_{στ}`, a 2-cocycle
inflated from `Gal(L/ℚ)` with `c(1,1) = 1`; and degree multiplicativity in the form
`|ker m_σ|·|ker m_τ| = c(σ,τ)⁴·|ker m_{στ}|` (`deg μ = |ker μ(ℚ̄)|` in characteristic 0,
`deg[n] = n⁴` on a surface); and algebraicity: `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite
surjective scheme morphism `F_σ : A → A`. -/
def ConjugacyData (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A))
    (c : GQ → GQ → ℚ) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, c σ τ ≠ 0 ∧ ∃ n d : ℤ, d ≠ 0 ∧ c σ τ = n / d ∧
      d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∀ σ τ ρ, c (σ * τ) ρ * c σ τ = c τ ρ * c σ (τ * ρ)) ∧
  (∀ σ σ' τ τ' : GQ, (∀ x ∈ L, act σ x = act σ' x) → (∀ x ∈ L, act τ x = act τ' x) →
      c σ τ = c σ' τ') ∧
  c 1 1 = 1 ∧
  (∀ σ τ, (Nat.card (m σ).ker : ℚ) * Nat.card (m τ).ker = c σ τ ^ 4 * Nat.card (m (σ * τ)).ker) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- The Galois action of `σ' ∈ Aut(ℚ̄/L)` on `A(ℚ̄)` is bijective. -/
theorem galAct_bijective {L : IF} (A : PkgI3.AbVar L) (σ' : Qbar ≃ₐ[L] Qbar) :
    Function.Bijective (A.galAct σ') := by
  have key : ∀ (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar),
      A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
    intro g h P
    show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
    rw [PkgI3.AbVar.galHom_mul, Category.assoc]
  have one : ∀ P : A.Pt Qbar, A.galAct 1 P = P := by
    intro P
    show PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  refine ⟨fun P Q h => ?_, fun Q => ⟨A.galAct σ'⁻¹ Q, ?_⟩⟩
  · have := congrArg (A.galAct σ'⁻¹) h
    rwa [key, key, inv_mul_cancel, one, one] at this
  · rw [key, mul_inv_cancel, one]

/-- `k ∈ G_L` as an `L`-automorphism of `ℚ̄`. -/
noncomputable def toLAut {L : IF} (k : GQ) (hk : k ∈ GQL L) : Qbar ≃ₐ[L] Qbar :=
  AlgEquiv.ofRingEquiv (f := (act k).toRingEquiv) (fun x => mem_GQL.mp hk x x.2)

theorem toLAut_apply {L : IF} (k : GQ) (hk : k ∈ GQL L) (x : Qbar) : toLAut k hk x = act k x :=
  rfl

/-- The kernel sizes of `m_k`, `m_{σk}`, `m_{kσ}` for `k ∈ G_L` (from the first two clauses of
`ConjugacyData`). -/
theorem card_ker_GL {L : IF} {A : PkgI3.AbVar L} {m : GQ → (PtQ L A →+ PtQ L A)}
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (σ k : GQ) (hk : k ∈ GQL L) :
    Nat.card (m k).ker = 1 ∧ Nat.card (m (σ * k)).ker = Nat.card (m σ).ker ∧
      Nat.card (m (k * σ)).ker = Nat.card (m σ).ker := by
  have hmk : m k = MonoidHom.toAdditive (A.galAct (toLAut k hk)) :=
    hgal k (toLAut k hk) (toLAut_apply k hk)
  have hbij : Function.Bijective (m k) := by
    rw [hmk]; exact galAct_bijective A (toLAut k hk)
  have hker : (m k).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : m k x = m k 0 := by rw [map_zero]; exact hx
    exact hbij.1 this
  refine ⟨by rw [hker]; simp, ?_, ?_⟩
  · rw [(hinfl σ k hk).1]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨m k x, x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hbij.1 (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨⟨x, hy⟩, rfl⟩
  · have hk2 : ((m k).comp (m σ)).ker = (m σ).ker := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply]
      constructor
      · intro h
        have : m k (m σ x) = m k 0 := by rw [map_zero]; exact h
        exact hbij.1 this
      · intro h; rw [h, map_zero]
    rw [(hinfl σ k hk).2, hk2]

/-- `a_σ = |ker m_σ|^{-1/4}` (`= (deg μ_σ)^{-1/4}`, N5 L645). -/
noncomputable def normA {L : IF} {A : PkgI3.AbVar L} (m : GQ → (PtQ L A →+ PtQ L A)) (σ : GQ) :
    ℝ := (Nat.card (m σ).ker : ℝ) ^ (-(1 / 4 : ℝ))

/-- **B1's normalization, proved** (N5 L645-663): from the conjugacy isogenies, `ε = sgn c` is a
normalized locally constant sign cocycle inflated from `Gal(L/ℚ)`, and `(m, a = |ker m|^{-1/4},
ε)` is a descent datum. -/
theorem descentDatum_of_conjugacy (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (c : GQ → GQ → ℚ)
    (h : ConjugacyData L A m c) : DescentDatum L A (fun σ τ => sgnU (c σ τ)) := by
  obtain ⟨hgal, hinfl, hend, hfin, hc, hcoc, hcinf, hc11, hdeg, halg⟩ := h
  have hkerL := card_ker_GL hgal hinfl
  have hcard : ∀ σ, 0 < Nat.card (m σ).ker := fun σ => by
    haveI : Finite (m σ).ker := (hfin σ).2.to_subtype
    exact Nat.card_pos
  -- the sign cocycle
  have hloc : IsLocallyConstant (Function.uncurry fun σ τ => sgnU (c σ τ)) := by
    refine isLocallyConstant_of_openSubgroup ((GQL L).prod (GQL L))
      (by rw [Subgroup.coe_prod]; exact L.fixingSubgroup_isOpen.prod L.fixingSubgroup_isOpen)
      _ ?_
    rintro ⟨σ, τ⟩ ⟨k₁, k₂⟩ hk
    rw [Subgroup.mem_prod] at hk
    simp only [Function.uncurry_apply_pair, Prod.mk_mul_mk]
    congr 1
    refine (hcinf σ (σ * k₁) τ (τ * k₂) ?_ ?_).symm
    · intro x hx
      show act σ x = act σ (act k₁ x)
      rw [mem_GQL.mp hk.1 x hx]
    · intro x hx
      show act τ x = act τ (act k₂ x)
      rw [mem_GQL.mp hk.2 x hx]
  refine ⟨⟨hloc, fun σ τ => sgnU_sq _, fun σ τ ρ => ?_⟩, ?_, ?_, m, normA m, ?_, ?_, hgal, hinfl,
    hend, hfin, ?_, halg⟩
  · rw [← sgnU_mul (hc _ _).1 (hc _ _).1, ← sgnU_mul (hc _ _).1 (hc _ _).1, hcoc]
  · exact fun σ σ' τ τ' h1 h2 => by simp only [hcinf σ σ' τ τ' h1 h2]
  · show sgnU (c 1 1) = 1
    rw [hc11]; unfold sgnU; simp
  · intro σ; unfold normA; exact Real.rpow_pos_of_pos (by exact_mod_cast hcard σ) _
  · intro σ k hk
    obtain ⟨h1, h2, h3⟩ := hkerL σ k hk
    unfold normA
    rw [h1, h2, h3]
    simp
  · intro σ τ
    obtain ⟨hc0, n, d, hd, hcnd, hnd⟩ := hc σ τ
    have hn : n ≠ 0 := by
      rintro rfl; apply hc0; rw [hcnd]; simp
    refine ⟨n, d, hn, hd, hnd, ?_⟩
    have hx : (0 : ℝ) < Nat.card (m σ).ker := by exact_mod_cast hcard σ
    have hy : (0 : ℝ) < Nat.card (m τ).ker := by exact_mod_cast hcard τ
    have hz : (0 : ℝ) < Nat.card (m (σ * τ)).ker := by exact_mod_cast hcard (σ * τ)
    have hdegR : (Nat.card (m σ).ker : ℝ) * Nat.card (m τ).ker =
        |(c σ τ : ℝ)| ^ 4 * Nat.card (m (σ * τ)).ker := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hdeg σ τ)
      push_cast at this
      rw [this, pow_abs, abs_of_nonneg (by positivity)]
    have hcR : ((n : ℝ) / d) = (c σ τ : ℝ) := by rw [hcnd]; push_cast; rfl
    have habs : (0 : ℝ) < |(c σ τ : ℝ)| := abs_pos.mpr (by exact_mod_cast hc0)
    have key : normA m σ * normA m τ * |(c σ τ : ℝ)| = normA m (σ * τ) := by
      unfold normA
      rw [← Real.mul_rpow hx.le hy.le, hdegR, Real.mul_rpow (by positivity) hz.le]
      rw [show |(c σ τ : ℝ)| ^ 4 = |(c σ τ : ℝ)| ^ ((4 : ℕ) : ℝ) by norm_cast,
        ← Real.rpow_mul habs.le]
      rw [show ((4 : ℕ) : ℝ) * (-(1 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    rw [hcR]
    have e1 : ((normA m σ * normA m τ * (c σ τ : ℝ) : ℝ) : ℂ) =
        ((sgnU (c σ τ) : ℂˣ) : ℂ) * ((normA m σ * normA m τ * |(c σ τ : ℝ)| : ℝ) : ℂ) := by
      have h := sgnU_mul_abs (c σ τ)
      push_cast at h ⊢
      linear_combination (-((normA m σ : ℂ) * (normA m τ : ℂ))) * h
    rw [e1, key]

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

theorem mem_GQL_bot (σ : GQ) : σ ∈ GQL (⊥ : IF) := by
  rw [mem_GQL]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact (act σ).commutes r

theorem galAct_mul {L : IF} (A : PkgI3.AbVar L) (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar) :
    A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
  show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

/-- **Sanity check (proved).** For every abelian variety `A` over `ℚ` (here `L = ⊥ ⊆ ℚ̄`), the
Galois action itself is a descent datum with `ε = 1`, `a = 1`, `F_σ = id`. So `DescentDatum` is
not contradictory. -/
theorem descentDatum_bot (A : PkgI3.AbVar (⊥ : IF)) : DescentDatum ⊥ A (fun _ _ => 1) := by
  let m : GQ → (PtQ ⊥ A →+ PtQ ⊥ A) := fun σ =>
    MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))
  have hmul : ∀ σ τ : GQ, (m σ).comp (m τ) = m (σ * τ) := by
    intro σ τ
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (A.galAct _ (A.galAct _ (Additive.toMul x))) =
      Additive.ofMul (A.galAct _ (Additive.toMul x))
    rw [galAct_mul]
    rfl
  have hbij : ∀ σ, Function.Bijective (m σ) := fun σ => galAct_bijective A _
  refine ⟨⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ => by simp⟩,
    fun _ _ _ _ _ _ => rfl, rfl, m, fun _ => 1, fun _ => one_pos, fun _ _ _ => ⟨rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
  · intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  · intro σ
    refine ⟨(hbij σ).2, ?_⟩
    have : ((m σ).ker : Set (PtQ ⊥ A)) = {0} := by
      ext x
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      constructor
      · intro h; exact (hbij σ).1 (h.trans (map_zero _).symm)
      · rintro rfl; exact map_zero _
    rw [this]; exact Set.finite_singleton 0
  · intro σ τ
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by rw [one_smul, one_smul, hmul], by simp⟩
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **G4's output (N5 L532-563 and the B1 normalization L632-663).** A finite Galois `L ⊆ ℚ̄`
(the Hom field) with `[L:ℚ] ≤ D`, unramified outside `T`, a QM model `A/L` of `P` (`IsQMModel`), and
the descent datum `ε` of `A` (`DescentDatum`). -/
def G4Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
    Module.finrank ℚ L ≤ heightD ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
    ∃ (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ), IsQMModel L A P ∧ DescentDatum L A ε

/-- **G7's output (B2-B3, N5 L664-716).** The data of G4 (`L`, `A/L`, `ε`), and: a Dirichlet
character `χ` mod `N`, a locally constant cochain `β : G_ℚ → ℂ^×` with `β² = χ` and `∂β = ε`, and
the kernel field `L' ⊇ L` of `β|_{G_L}`: finite Galois, `G_{L'} = G_L ∩ ker β`,
`[L':ℚ] ≤ Q_D · M_{S_mul}(u)`, and the base change `A_{L'}` is a model of `P`'s surface. -/
def G7Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ),
    IsQMModel L A P ∧ DescentDatum L A ε ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
    (∀ x y, β x * β y = ε x y * β (x * y)) ∧
    (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
    (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-! ## Transitivity of base change -/

/-- `(A_{L'})_{ℚ̄} ≅ A_{ℚ̄}` for `L ≤ L' ⊆ ℚ̄` (pasting of pullbacks). -/
noncomputable def baseChangeTrans {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) :
    ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)).baseChange Qbar).X ≅
      (A.baseChange Qbar).X := by
  letI := incAlg h
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L L')) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp]
    congr 1
  exact ((Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)))
      (Spec.map (CommRingCat.ofHom (algebraMap L L')))).app A.X).symm ≪≫
    eqToIso (congrArg (fun f => (Over.pullback f).obj A.X) hcomp)

theorem isModelOver_baseChange {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) (P : QML3 Qbar)
    (hA : IsModelOver L A P) :
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)) P := by
  obtain ⟨e⟩ := hA
  exact ⟨baseChangeTrans h A ≪≫ e⟩

theorem IsQMModel.isModelOver {L : IF} {A : PkgI3.AbVar L} {P : QML3 Qbar}
    (h : IsQMModel L A P) : IsModelOver L A P := by
  obtain ⟨K, hKL, PK, hPK, rfl⟩ := h
  exact isModelOver_baseChange hKL PK.A P hPK

/-! ## G7 from G4 (proved) -/

/-- `max S_mul ≤ D` (copied from `ZInQKernel/Main.lean`, `ZInQ.Mult.le_heightD_of_mem_S_mul`). -/
theorem le_heightD_of_mem_S_mul {p : ℕ} (hp : p ∈ Mult.S_mul) : p ≤ heightD :=
  (Mult.le_R_of_mem_S_mul hp).trans_eq ((Size.R_eq_D catalogueBound8).trans Mult.D_eq_heightD)

theorem admissible_S_mul :
    (∀ p ∈ Mult.S_mul, p.Prime) ∧ (∀ p ∈ Mult.S_mul, (p : ℝ) ≤ (heightD : ℝ)) ∧
      (10 : ℝ) ^ 12 ≤ (heightD : ℝ) :=
  ⟨fun _ hp => Mult.prime_of_mem_S_mul hp,
   fun _ hp => by exact_mod_cast le_heightD_of_mem_S_mul hp,
   by exact_mod_cast Compiler.Precision.ten_pow_twelve_le_heightD⟩

/-- **G7 (B2-B3 on the actual descent datum), proved** from G4's output and glue-descent's four
B2 leaves, by `GlueDescent.B3Q.b3_degree_le_QM` at `S = S_mul`, `R = D`, `η = 1`. -/
theorem g7Out_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_degree_le_QM hHasse hTwo hSq hUnr Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u L hLD
      ε hε hinf h11 hram 1 (fun _ => by simp) (IsLocallyConstant.const 1)
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, isModelOver_baseChange hle A P hA.isModelOver⟩

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-- **B2 over `G_ℚ` with the level of `χ` exposed** (the proof of
`GlueDescent.B2Q.b2_of_leaves`, copied; the only change is the extra output
`N = chiLevel T₋ = ∏_{p ∈ T₋} lev p` with `T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`). -/
theorem b2_of_leaves_level (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∃ Tm ⊆ T, N = chiLevel Tm) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  classical
  let Tm := T.filter (fun p => ∃ hp : p.Prime, ¬ SignCob (pull (resp ⟨p, hp⟩) ε))
  have hloc : ∀ p : Nat.Primes, ¬ SignCob (pull (resp p) ε) ↔ (p : ℕ) ∈ Tm := by
    intro p
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨?_, p.2, h⟩
      by_contra hpT
      exact h (hUnr L ε hε hinf p (hram p hpT))
    · intro h
      obtain ⟨_, hp, h'⟩ := Finset.mem_filter.1 h
      exact h'
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => hT q (Finset.filter_subset _ _ hq)
  haveI hN : NeZero (chiLevel Tm) := ⟨(chiLevel_pos Tm hTmP).ne'⟩
  obtain ⟨_, hsupp, hord⟩ := exists_chi T Tm hT (Finset.filter_subset _ _)
  let χ := chi Tm
  let β₀ : GQ → ℂˣ := fun x => sqrtU (galChar χ x)
  have hβ₀ : ∀ x, β₀ x ^ 2 = galChar χ x := fun x => sqrtU_sq _
  have hl : IsLocallyConstant β₀ := (galChar_isLocallyConstant χ).comp sqrtU
  have agree : ∀ p : Nat.Primes,
      SignCob (pull (resp p) ε) ↔ SignCob (pull (resp p) (dB β₀)) := by
    intro p
    rw [pull_dB, signCob_dB_iff ((galChar χ).comp (resp p)) (β₀ ∘ resp p) (fun x => hβ₀ _)
      (hl.comp_continuous (resp_continuous p))]
    obtain ⟨u, hu1, hu2⟩ := exists_crt_unit (chiLevel Tm) p p.2
    have hsq := hSq p (chiLevel Tm) χ u hu1 hu2
    have hsq' : (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
        ∀ x, φ x ^ 2 = ((galChar χ).comp (resp p)) x) ↔ χ.toUnitHom u = 1 := hsq
    rw [hsq', chi_toUnitHom_crt Tm hTmP p p.2 u hu1 hu2]
    by_cases h : (p : ℕ) ∈ Tm
    · rw [if_pos h]
      have hne : (-1 : ℂˣ) ≠ 1 := by
        intro h1
        have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        norm_num at this
      constructor
      · intro hc; exact absurd hc ((hloc p).mpr h)
      · intro h1; exact absurd h1 hne
    · rw [if_neg h]
      simp only [iff_true]
      by_contra hc
      exact h ((hloc p).mp hc)
  obtain ⟨β, hβl, hβs, hβe⟩ := exists_beta (G := GQ) GQp resp resp_continuous hHasse hTwo ε hε
    (galChar χ) β₀ hβ₀ hl agree
  exact ⟨chiLevel Tm, hN, χ, β, ⟨Tm, Finset.filter_subset _ _, rfl⟩, hsupp, hord, hβl, hβs, hβe⟩

/-- **B3 from a given B2 cochain** (the proof of `GlueDescent.B3Q.b3_of_leaves`, copied, with
`b2_of_leaves`' output taken as hypotheses so that the twist `η` may depend on it). -/
theorem b3_of_cochain
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β₁ : GQ → ℂˣ) (hβl₁ : IsLocallyConstant β₁)
    (hβs₁ : ∀ x, β₁ x ^ 2 = galChar χ x) (hβe₁ : ∀ x y, β₁ x * β₁ y = ε x y * β₁ (x * y))
    (tw : GQ →* ℂˣ) (htw : ∀ x, tw x ^ 2 = 1) (htwl : IsLocallyConstant tw) :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ),
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β₁ σ * tw σ = 1) ∧
      Module.finrank ℚ L' ≤ 2 * orderOf χ * Module.finrank ℚ L := by
  let β : GQ → ℂˣ := fun x => β₁ x * tw x
  have hβl : IsLocallyConstant β := hβl₁.mul htwl
  have hβs : ∀ x, β x ^ 2 = galChar χ x := twist_sq (galChar χ) hβs₁ tw htw
  have hβe : ∀ x y, β x * β y = ε x y * β (x * y) := twist hβe₁ tw
  have hεN := inflatedNormalized_of L ε hε hinf h11
  have hβ : IsCochainFor ε β := hβe
  let K' : Subgroup GQ := kernelSubgroup hβ hεN
  have hHopen : IsOpen ((GQL L : Subgroup GQ) : Set GQ) := L.fixingSubgroup_isOpen
  have hK'set : (K' : Set GQ) = (GQL L : Set GQ) ∩ β ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_kernelSubgroup hβ hεN
  have hK'open : IsOpen (K' : Set GQ) := by
    rw [hK'set]; exact hHopen.inter (hβl.isOpen_fiber 1)
  have hK'closed : IsClosed (K' : Set GQ) := Subgroup.isClosed_of_isOpen K' hK'open
  let K'c : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toSubgroup := K', isClosed' := hK'closed }
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField K'
  have hfix : L'.fixingSubgroup = K' := InfiniteGalois.fixingSubgroup_fixedField K'c
  have hGL' : ∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1 := by
    intro σ
    show σ ∈ L'.fixingSubgroup ↔ _
    rw [hfix]
    exact mem_kernelSubgroup hβ hεN
  have hm := orderOf_pos_dirichlet χ
  have hpow : ∀ s ∈ GQL L, β s ^ (2 * orderOf χ) = 1 := by
    intro s _
    rw [pow_mul, hβs]
    show (MulChar.mulEquivToUnitHom χ (cyc N s)) ^ orderOf χ = 1
    rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]
  haveI : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hidx := index_kernel_le hβ hεN (2 * orderOf χ) (by positivity) hpow
  have hfd : FiniteDimensional ℚ L' :=
    (InfiniteGalois.isOpen_iff_finite L').mp (by rw [hfix]; exact hK'open)
  have hL : Module.finrank ℚ L = (GQL L).index := IntermediateField.finrank_eq_fixingSubgroup_index
      (L := L)
  have hL' : Module.finrank ℚ L' = K'.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := L'), hfix]
    rfl
  have hgal : IsGalois ℚ L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp (by rw [hfix]; exact kernelSubgroup_normal hβ hεN)
  have hle : L ≤ L' := by
    intro x hx
    show x ∈ IntermediateField.fixedField K'
    exact fun k => mem_GQL.mp (kernelSubgroup_le hβ hεN k.2) x hx
  refine ⟨L', hle, hfd, hgal, hGL', ?_⟩
  rw [hL', hL]; exact hidx

theorem two_mem_T (u : ℚ) : 2 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_two (by norm_num))

/-- **The data of G7, clause by clause** (the interface handed to G8-G16). For the fibre `P`
over `J(u)`: the Hom field `L` (finite Galois, unramified outside `T`), the model `A/L` with its
descent datum `ε` (B1), the Dirichlet character `χ` mod `N` (`N = ∏_{p ∈ T₋} lev p` for some
`T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`: `χ` is a product of odd characters mod `p` and mod `4`, N5
L677-683, which bounds the conductor of `β` at every prime, as G15 needs), the
cochain `β` (locally constant, `β² = χ`, `∂β = ε`, twisted so that inertia outside `T` dies), and
the kernel field `L' ⊇ L` of `β|_{G_L}`: `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M_{S_mul}(u)`,
`L'` unramified outside `T` (Galois form), and `A_{L'}` a model of `P`'s surface. -/
def G7Data (u : ℚ) (P : QML3 Qbar) (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ)
    [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF) (hLL' : L ≤ L') : Prop :=
  IsQMModel L A P ∧ DescentDatum L A ε ∧
  (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T u) ∧
  (∃ Tm ⊆ T u, N = chiLevel Tm) ∧
  IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
  (∀ x y, β x * β y = ε x y * β (x * y)) ∧
  (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
  (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-- **G7's output with the twist** (N5 L702-716): the data of `G7Data` exist. -/
def G7OutUnr (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL'

/-- **G7 with the twist, proved** from G4's output and the four B2 leaves: B2
(`b2_of_leaves`), the twist killing inertia outside `T` (`GlueB3Unram.unramified_outside_noLeaf`,
no leaf), B3 (`b3_of_cochain`) and the constants (`degree_le_QM`). -/
theorem g7OutUnr_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7OutUnr u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  have hT : ∀ p ∈ T u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β₁, hlev, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves_level hHasse hTwo hSq hUnr L ε hε hinf (T u) hT hram
  have hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1 :=
    inflatedNormalized_of L ε hε hinf h11
  obtain ⟨Q, -, hη, hηl, hunr⟩ := GlueB3Unram.unramified_outside_noLeaf L (T u) (two_mem_T u)
    hram ε hεN χ hsupp β₁ hβl₁ hβs₁ hβe₁
  obtain ⟨L', hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_of_cochain L ε hε hinf h11 χ β₁ hβl₁ hβs₁ hβe₁ _ hη hηl
  have hdegR := degree_le_QM Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u
    (Module.finrank ℚ L) (orderOf χ) hLD hord
  refine ⟨L, hfd, hgal, A, ε, N, hN, χ, fun x => β₁ x * (∏ q ∈ Q, GlueB3Unram.etaP q) x,
    L', hfd', hgal', hle, hA, hD, hram, hsupp, hlev, hβl₁.mul hηl, twist_sq (galChar χ) hβs₁ _ hη,
    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := hdegR

theorem g7Out_of_g7OutUnr (u : ℚ) (P : QML3 Qbar) (h : G7OutUnr u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hA, hD, hram, -, -, hβl, hβs,
    hβe, hGL', hdeg, -, hM⟩ := h
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, hM⟩

/-! ## G2's bookkeeping (proved) -/

/-- **G2's input, the fibre cover (Prop. TS + Lemma NV, N5 L509-529; remaining).** There is a
separable `f ∈ ℚ[X]` of degree `≤ 324` (the fibre of the normalized cover of `P¹_u` over `u`)
whose splitting field `K = ℚ(roots of f) ⊆ ℚ̄` is unramified outside `T` and contains the residue
field of the point of `P` (a rational fibre `PK/K`, `RationalFibre`). -/
def FibreCoverOut (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) :
    Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    ∃ PK : QML3 (IntermediateField.adjoin ℚ (f.rootSet Qbar)),
      RationalFibre Y Φ P (IntermediateField.adjoin ℚ (f.rootSet Qbar)) PK

/-- **G2, proved from the fibre cover**: the splitting field is Galois of degree `≤ 324!`
(`GlueRepo.Numerics.splitting_degree_le`). -/
theorem g2Out_of_cover (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ)
    (P : QML3 Qbar) (h : FibreCoverOut Y Φ u P) : G2Out Y Φ u P := by
  obtain ⟨f, hs, hd, hram, A, hA⟩ := h
  have hsp : f.IsSplittingField ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  have hgal : IsGalois ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IsGalois.of_separable_splitting_field hs
  have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) ≤ heightF0 := by
    rw [(Polynomial.IsSplittingField.algEquiv _ f).toLinearEquiv.finrank_eq]
    exact GlueRepo.Numerics.splitting_degree_le f hs hd
  exact ⟨_, hfd, hgal, hdeg, hram, A, hA⟩

/-! ## G4's bookkeeping (proved) -/

/-- **Compositum of unramified fields (STANDARD; remaining, not in Mathlib v4.35).** If `E`
and `K` are finite over `ℚ` and unramified at `p`, so is `E ⊔ K` (Neukirch, *Algebraic Number
Theory*, I (8.?)/III, UNVERIFIED locator; a prime is unramified in a compositum iff it is in both
factors, for Galois factors). -/
def UnramifiedSup : Prop :=
  ∀ (E K : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ K] [IsGalois ℚ E] [IsGalois ℚ K]
    (p : ℕ), UnramifiedAt E p → UnramifiedAt K p → UnramifiedAt (E ⊔ K) p

/-- **G4's input, the kernel field (N5 L540-563 and B1, L632-663; remaining).** For a field `K`
and model `A/K` as in G2's output: `W₀ = Res_{K/ℚ} A` has endomorphism lattice of rank `r ≤ 16F₀²`;
the image of `G_ℚ` on it is a finite subgroup `G ≤ GL_r(ℤ)` with kernel field `E`
(`[E:ℚ] = |G|`), unramified outside `T` (inertia at `p ∉ T` acts trivially on the Tate module of
`W₀`, which has good reduction there); and the base change `A_L` of `A` to the Hom field
`L = E ⊔ K` carries conjugacy isogenies `μ_σ : ^σA → A` over `L`, `B`-linear after the
Skolem-Noether correction, with rational discrepancy (`ConjugacyData`; B1's normalization to a
sign cocycle is proved, `descentDatum_of_conjugacy`). -/
def KernelFieldOut (u : ℚ) (P : QML3 Qbar) (K : IF) (A : PkgI3.AbVar K) : Prop :=
  ∃ (r : ℕ), r ≤ 16 * heightF0 ^ 2 ∧
  ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IF) (_ : FiniteDimensional ℚ E)
    (_ : IsGalois ℚ E), Module.finrank ℚ E = Nat.card G ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt E p) ∧
    ∃ (m : GQ → (PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) →+
        PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right))))
      (c : GQ → GQ → ℚ),
      ConjugacyData (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) m c

/-- **G4, proved from the kernel field**: `L = E ⊔ K` is finite Galois, unramified outside `T`
(`UnramifiedSup`), `[L:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D` (Minkowski,
`GlueRepo.TorsionFree.card_le_three_pow`; `GlueRepo.Numerics.a8_field`), `A_L = (PK.A)_L` is a QM
model of `P` (`IsQMModel`), and B1's normalization gives the descent datum
(`descentDatum_of_conjugacy`). -/
theorem g4Out_of_kernelField (hSup : UnramifiedSup) (u : ℚ) (P : QML3 Qbar) (K : IF)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hK : Module.finrank ℚ K ≤ heightF0)
    (hramK : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) (PK : QML3 K)
    (hPK : IsModelOver K PK.A P) (h : KernelFieldOut u P K PK.A) : G4Out u P := by
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hCD⟩ := h
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hK hE hr
  have : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  exact ⟨E ⊔ K, inferInstance, inferInstance, hdeg,
    fun p hp => hSup E K p (hramE p hp) (hramK p hp), _, _,
    ⟨K, le_sup_right, PK, hPK, rfl⟩, descentDatum_of_conjugacy _ _ m c hCD⟩

/-! ## The remaining glue as Props, and the composite -/

/-- **Remaining (G2): Prop. TS + Lemma NV on the actual fibre** (h-decomposition G2: inputs
R1(d), R2, T1, T2; the valuation case analysis is proved, `GlueRepo.PR.inertia_orders_eq_one_iff`,
and Lemma NV step 2, `LeafQM.AV.residue_unramified_over_branch`). -/
def FibreCoverExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P → FibreCoverOut Y Φ u P

/-- **Remaining (G4 + B1): the kernel field of `Res_{K/ℚ} A` and the descent datum on the Hom
field**, for every field `K` and rational fibre `PK/K` as in G2's output (h-decomposition G4: inputs R2, R3, T6,
R7a, T28; A7 proved, `LeafQM.AV.fibre_conjugates_isomorphic`; B1's algebra proved,
glue-descent `B1Quat`, `Cochain`; uses NoCM (G6) for `End⁰(A_ℚ̄) = B`). -/
def KernelFieldExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK → KernelFieldOut u P K PK.A

/-- **G2 → G4 → G7 (proved)**: from the two remaining glue Props and the four B2 leaves, every
fibre context has G7's output. -/
theorem fieldDescent (hCover : FibreCoverExists) (hKer : KernelFieldExists) (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7Out u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7Out_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-- **G2 → G4 → G7 with the twist (proved)**: as `fieldDescent`, with `L'` unramified outside `T`
and the clause list `G7Data`. -/
theorem fieldDescentUnr (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7OutUnr_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-! ## How G7's output feeds `ModularConstituent` -/

/-- (copied from scratch/g0-split/part_split.lean, `G0Split.CommonConstituent`, verbatim) The
hypotheses of E1: for some prime `ℓ` and field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a
common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- A finite-dimensional `L ⊆ ℚ̄` is a number field. -/
theorem numberField_of_fd (L : IF) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- **`ModularConstituent`** (scratch/g0-split/part_split.lean, piece 10), copied with
def-faltings' copy `ZInQ.DefFaltings.AbVar` and the bridge `LeafAdopt.abVarEquiv` (the identity on
the underlying scheme) replaced by the kernel's `PkgI3.AbVar`, which `ZInQKernel/HDecomp/`
already uses for both. -/
def ModularConstituentG : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : PkgI3.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent A (J.baseChange L.K)

/-- **The remaining ranges G8-G16 (the next tasks' target), as one Prop.** For every fibre
context and every G7 data (`G7Data`): a level `1 ≤ M ≤ Q_D·M_{S_mul}(u)²`, a `J₁(M)` over `ℚ`, and a
common constituent of `V_ℓ(A_{L'})` and `V_ℓ(J₁(M)_{L'})` as `G_{L'}`-representations (G8: `ρ_ℓ`
from `β`, `a_σ`, `m_σ`; G9-G12: de Rham, odd, modular; G13-G16: newform, level, Eichler-Shimura). -/
def AfterG7 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ (M : ℕ) (J : PkgI3.AbVar ℚ), 0 < M ∧ LeafModCurves.IsJ1 M J ∧
      (M : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      @CommonConstituent L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) (J.baseChange L')

/-- **`ModularConstituent` from this range and the next (proved)**: G2, G4, G7 here
(`fieldDescentUnr`) and the ranges G8-G16 as `AfterG7`. -/
theorem modularConstituent_of_ranges (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  have hctx : FibreCtx Y Φ π u P := ⟨h1, h2, hu, y, hy, hπ⟩
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hdata⟩ :=
    fieldDescentUnr hCover hKer hSup hHasse hTwo hSq hUnr Y Φ π u P hctx
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ := hRest Y Φ π u P hctx L A ε N χ β L' hle hdata
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨⟨L'⟩, algebraMap L' Qbar, @PkgI3.AbVar.baseChange L _ A L' _ (incAlg hle), M, J,
    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩

/-- **The same, with glue-descent's `LeafHasse`, `LeafLocalTwo` replaced by the bundle's T14-T15**
(`PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`; `GlueWP3.leafHasse_of_T14`,
`leafLocalTwo_of_T15`). -/
theorem modularConstituent_of_ranges_T14 (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup) (hH : PkgI6.BrauerHasse2C) (hR : PkgI6.BrauerReciprocity2C)
    (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG :=
  modularConstituent_of_ranges hCover hKer hSup (GlueWP3.leafHasse_of_T14 hH hR)
    (GlueWP3.leafLocalTwo_of_T15 hC) hSq hUnr hRest

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

/-- (copied) The restriction map `G_K → G_ℚ` (Mathlib's `Field.absoluteGaloisGroup.map`). -/
noncomputable def resQ (K : Type) [Field K] [NumberField K] :
    Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
noncomputable def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied) g0-mod-galois' input "output of G2": inertia at `p ∉ T` lies in `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- (copied) g0-mod-galois' input "output of G7 at the coefficient prime `ℓ`". -/
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

end GaloisCopy

/-- **Bridge 1 (Mathlib-level Galois theory; proved below, `resQRange`).** For a finite Galois `L' ⊆ ℚ̄`, the
image of `resQ L' : G_{L'} → G_ℚ` is `G_{L'} = Fix(L')` (true for every embedding of the
algebraic closures because `L'/ℚ` is normal). -/
def ResQRange : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'],
    (@GaloisCopy.resQ L' _ (numberField_of_fd L')).range = L'.fixingSubgroup

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (GaloisCopy.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@GaloisCopy.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (GaloisCopy.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : Qbar ≃ₐ[ℚ] Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x


theorem resQRange : ResQRange := fun L' _ _ => resQ_range L'

/-- **g0-mod-galois' `G2Out` for `K = L'`, proved** from `G7Data` (B3(v): inertia outside `T`
fixes `L'`) and `ResQRange`. -/
theorem galoisG2Out_of_g7Data (hRes : ResQRange) (u : ℚ) (P : QML3 Qbar) (L : IF)
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (h : G7Data u P L A ε N χ β L' hLL') :
    @GaloisCopy.G2Out L' _ (numberField_of_fd L') (T u) := by
  intro p hp hpT v hv σ hσ
  rw [hRes L']
  have hv' : GlueB3Unram.LiesOver v p := hv
  exact h.2.2.2.2.2.2.2.2.2.2.1 p hp hpT v hv' (Subgroup.mem_map_of_mem _ hσ)

/-- **Bridge 2 (remaining; the Tate functor on the descent datum, §3 of the report).** From G7's
data, the rank-4 endomorphism ring and `dim A_{L'} = 2` (G5-G6, A9; `model_dim`), for every `ℓ`:
operators `Tm σ` (`ℚ̄_ℓ ⊗ T_ℓ(m_σ)` transported to `V_ℓ(A_{L'})`), `c = n/d`, `a`, `ε`, `β` mapped
into `ℚ̄_ℓ` by one embedding of the number field they generate, and matrix units of
`End_{L'}(A) ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`, satisfying g0-mod-galois' `G7Out`. -/
def TateBridge : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu

end G0ModField
end G0ModFieldSec

/-! ## g0-mod-newform: scratch/g0-mod-newform/part_new.lean, verbatim minus `#print axioms`, with two
changes: `LeafModCurves` is opened with `hiding` (as leaf-adopt3 did for `C9Rhof`), and
`ZInQ.Mult.le_heightD_of_mem_S_mul` (in `ZInQKernel/Main.lean`, not imported) is replaced by
g0-mod-field's verbatim copy `G0ModField.le_heightD_of_mem_S_mul` (same statement). -/
section G0ModNewformSec
/-!
# g0-mod-newform: glue G13-G16 of `docs/research/h-decomposition.md` §3

The last range of `ModularConstituent` (`scratch/g0-split/part_split.lean`, piece 10): from the
outputs of G8-G12 (the constituent `r_ℓ` of `V_ℓ(A)` as a `G_ℚ`-representation, and Pan-Berger's
eigenform up to a finite twist, `G12Out`) to the outputs of G16 (a newform `f` of weight 2 and
level `1 ≤ N ≤ Q_R M²`, and for every `J₁(N)` a common constituent of `V₅(A)` and
`V₅(J₁(N)_{L'})`, E1's hypothesis).

* G13 (`g13`, proved from T24, T25, R16, Faltings' Satz 3 and 4, I3.M0, T18, T19):
  `r₅` is attached to a newform `f` outside a finite set, and `r₅|G_{L'} ≅ ρ_{f,5}|G_{L'}` is a
  common constituent of `V₅(A)` and `V₅(J₁(N)_{L'})`.
* G14 (`g14`, proved from R14, T18, T19 and the named AV-side Prop `G14TraceCompat`):
  `r₃` is attached to the same `f` outside a finite set, and `r₃`, `r₅` are isomorphic to R14's
  semisimple representations attached to `f` (in `AttachedTo` form, unramified outside `Nℓ`).
* G15 (`g15`, proved from R17 (`CarayolR17'`), the glue `SwanIndependent` and the named Prop
  `G15LocalBounds`): the exponents of `N` (`r₅` at `p ≠ 5`, `r₃` at `p = 5`).
* G16 (`g16`, proved: `GlueConductor.level_le`): `N ≤ Q_R M²`.

Leaves and glue targets are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
-- g0-assemble (as leaf-adopt3 did for C9Rhof): `LeafModCurves` opened with `hiding`, since
-- Leaves.lean has `LeafModCurves` copies of these `PkgI4` names (the kernel has none)
open PkgI3 PkgI3.AbVar C9Rhof
open LeafModCurves hiding Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform
  scaleH oldSpace IsNewform
open CategoryTheory AlgebraicGeometry

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-! ## §1. Representation lemmas (proved) -/

section RepLemmas

variable {k G V W : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- An isomorphism of `k[G]`-modules `ρ.asModule ≅ σ.asModule` is a `G`-equivariant
`k`-linear equivalence `V ≃ W`. -/
theorem equivariant_of_asModule (ρ : Representation k G V) (σ : Representation k G W)
    (φ : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  refine ⟨{ toFun := fun v => σ.asModuleEquiv (φ (ρ.asModuleEquiv.symm v))
            invFun := fun w => ρ.asModuleEquiv (φ.symm (σ.asModuleEquiv.symm w))
            map_add' := fun v w => by simp
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul]
              simp
            left_inv := fun v => by simp
            right_inv := fun w => by simp }, fun g v => ?_⟩
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul]
  simp

end RepLemmas

/-! ## §2. The conductor exponent at a level is invariant under isomorphism (proved) -/

section CondIso

open LadicCond
open PkgI4 (GQp)

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] {n : ℕ}

/-- If `e` intertwines `ρ` and `ρ'`, then `e` maps `V^{ρ(S)}` onto `V^{ρ'(S)}`. -/
theorem invariants_eq_map (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    invariants ρ' S = (invariants ρ S).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) := by
  ext w
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, by simp⟩
    intro σ hσ
    apply e.injective
    rw [← he, e.apply_symm_apply]
    exact hw σ hσ
  · rintro ⟨v, hv, rfl⟩ σ hσ
    change (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) = e v
    rw [he]
    exact congrArg e (hv σ hσ)

theorem codimInv_eq (ρ ρ' : GQp p →* GL (Fin n) k) (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (S : Set (GQp p)) :
    codimInv ρ' S = codimInv ρ S := by
  unfold codimInv
  rw [invariants_eq_map ρ ρ' e he S, LinearEquiv.finrank_map_eq]

theorem eq_one_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (σ : GQp p) (h : ρ σ = 1) : ρ' σ = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [Matrix.toLin'_apply, he, h]
  simp

theorem isAdapted_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) (hL : IsAdapted L ρ) :
    IsAdapted L ρ' :=
  ⟨hL.1, fun σ hσ => eq_one_of_intertwine ρ ρ' e he σ (hL.2 σ hσ)⟩

theorem condAt_eq_of_intertwine (ρ ρ' : GQp p →* GL (Fin n) k)
    (e : (Fin n → k) ≃ₗ[k] (Fin n → k))
    (he : ∀ σ v, (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec (e v) =
      e ((ρ σ : Matrix (Fin n) (Fin n) k).mulVec v)) (L : Fld p) :
    condAt L ρ' = condAt L ρ := by
  unfold condAt swanAt
  rw [codimInv_eq ρ ρ' e he]
  congr 1
  exact finsum_congr fun i => by rw [codimInv_eq ρ ρ' e he]

/-- An equivariant equivalence of `GaloisRep`s intertwines their restrictions to `G_{ℚ_p}`. -/
theorem restrictLocal_intertwine {ℓ : ℕ} [Fact ℓ.Prime] (r ρ : GaloisRep ℓ n)
    (e : (Fin n → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin n → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) :
    ∀ σ v, ((ρ.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec (e v) =
      e (((r.restrictLocal p) σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).mulVec v) := by
  intro σ v
  have h := he (PkgI4.decomp p σ) v
  rw [toRep_apply, toRep_apply, Matrix.toLin'_apply, Matrix.toLin'_apply] at h
  exact h.symm

end CondIso

/-! ## §3. The interface: data and outputs of G8-G12 -/

/-- **Pan-Berger's output on `r` (C7-C8 = G12's output, `docs/research/h-decomposition.md` §3).**
`r` is attached, up to the twist `ψ` and outside a finite set `S`, to a normalized eigenform `g`
of **weight 2** and level `M` (Pan's trace form, `PkgI4.GaloisRep.AttachedUpToTwist`), and `ψ` is,
at arithmetic Frobenius outside `S`, the Dirichlet character `ψD` mod `m` (N5 L758-768: the twist
is finite, then class field theory over `ℚ`; the weight comparison forces `k = 2`). -/
def PanOutput {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (r : GaloisRep ℓ 2) : Prop :=
  ∃ (M : ℕ) (χg : DirichletCharacter ℂ M) (g : CF M 2) (m : ℕ) (ψD : DirichletCharacter ℂ m)
    (ψ : GaloisChar ℓ) (S : Finset ℕ),
    0 < M ∧ IsNormalizedEigenform g χg ∧ 0 < m ∧ r.AttachedUpToTwist ψ ιC ιL g S ∧
    ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
      ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
        (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **`r|_{G_L}` is a constituent of `V_ℓ(A) ⊗ ℚ̄_ℓ`** (G8's `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}`): a
nonzero subrepresentation `U` of `V_ℓ(A) ⊗ ℚ̄_ℓ` (`A` over `L`) with a linear isomorphism
`U ≃ ℚ̄_ℓ²` carrying `τ ∈ G_L` to `r(σ)` for every `σ ∈ G_ℚ` with `i ∘ σ = τ ∘ i`
(`i : ℚ̄ → L̄`; such `σ` exist and are unique, `E1Sub.exists_res`). -/
def IsConstituentOf (ℓ : ℕ) [Fact ℓ.Prime] {L : Type} [Field L] [Algebra ℚ L] (A : AbVar L)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) (r : GaloisRep ℓ 2) : Prop :=
  ∃ (U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ)), U ≠ ⊥ ∧
    ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ), (∀ x, i (σ x) = τ (i x)) →
      ∀ u : U.toSubmodule,
        e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u, U.apply_mem_toSubmodule τ u.2⟩ =
          toRep r σ (e u)

/-- The data that G8-G12 produce for the model `A/L'`: an embedding `i : ℚ̄ → L̄'`, embeddings
`ιC : ℚ̄ → ℂ`, `ι₅ : ℚ̄ → ℚ̄₅`, `ι₃ : ℚ̄ → ℚ̄₃`, and the two `G_ℚ`-representations `r₅`, `r₃`
(N5 L719-734: `r_ℓ`, made a `G_ℚ`-representation by the Tate action and the descent of G7). -/
structure ModData (L : Type) [Field L] [NumberField L] (A : AbVar L) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L
  ιC : Qbar →ₐ[ℚ] ℂ
  ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3
  r5 : GaloisRep 5 2
  r3 : GaloisRep 3 2

/-- **G12Out: the output of G8-G12** (the range of task g0-mod-galois) on the data `D`:
`r₅`, `r₃` irreducible (C2, Burnside form), constituents of `V₅(A)`, `V₃(A)` on `G_{L'}` (C1),
and Pan-Berger's weight-2 eigenform up to a finite twist for `r₅` (C3-C8). -/
def G12Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) : Prop :=
  D.r5.IsIrreducible ∧ D.r3.IsIrreducible ∧ IsConstituentOf 5 A D.i D.r5 ∧
    IsConstituentOf 3 A D.i D.r3 ∧ PanOutput D.ιC D.ι5 D.r5

/-- `G12Out A`: some data `D` for `A` satisfy `G12Spec`. -/
def G12Out {L : Type} [Field L] [NumberField L] (A : AbVar L) : Prop :=
  ∃ D : ModData L A, G12Spec D

/-- **Open part of G14 (glue, AV side; N5 L776-795).** At every arithmetic Frobenius `τ` above
`p ∉ S`, the traces of `r₅` and `r₃` are the images of one algebraic number: if
`tr r₅(τ) = ι₅(c)` then `tr r₃(τ) = ι₃(c)`. Glazer's proof: for `p ∉ T ∪ {3, 5}` a lift `σ` of
Frobenius, the relative Frobenius of the reduction of `A` composed with `μ̄_σ` is an endomorphism
of `Ā_v` whose characteristic polynomial on `V_ℓ` is independent of `ℓ` (T7, with T3, T4); half
its trace times `β(σ)⁻¹a_σ` is the common value. It is a statement about the `r_ℓ` built in G8
from the descent data of G7 (not about arbitrary constituents: a constituent determines `r_ℓ`
only on `G_{L'}`), so it is to be proved together with that construction. -/
def G14TraceCompat {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p → ∀ c : Qbar,
      (D.r5.mat τ).trace = D.ι5 c → (D.r3.mat τ).trace = D.ι3 c

/-- Glazer's local bound for `r` at `p` (N5 L798-852), at a level `L_p` adapted to `r|G_{ℚ_p}`:
the conductor exponent is `≤ E₀` if `p ≤ R` (`R = D`), `≤ 2` if `p > R`, and `0` if
`p ∉ T = S ∪ supp M_S(u)`. -/
def LocalBound (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ∃ Lp : LadicCond.Fld p, LadicCond.IsAdapted Lp (r.restrictLocal p) ∧
    ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      LadicCond.condAt Lp (r.restrictLocal p) ≤ (ZInQ.heightE0 : ℚ)) ∧
    ((ZInQ.heightD : ℝ) < p → LadicCond.condAt Lp (r.restrictLocal p) ≤ 2) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u →
      LadicCond.condAt Lp (r.restrictLocal p) = 0)

/-- **Open part of G15 (glue, D1-D4 on the actual `A`; N5 L796-852).** `r₅` satisfies Glazer's
local bound at every prime `p ≠ 5` and `r₃` at `p = 5`. The cores are proved over the kernel's
finite-level objects (D1 `GlueConductor.D1_genuine`, D2 `PkgI2.D2_fixed_of_raynaud`, D3
`GlueConductor.fourth_pow_mem`, D4 `PkgI6.artinConductor_le_of_upper`,
`LadicCond.condAt_le_of_upper`); what is open is their instantiation on the `r_ℓ` built in G8
(Raynaud's semistability over `L'_v(A[3])`, wild inertia on `V_ℓ(A)`, the wild part of `β`). -/
def G15LocalBounds {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalBound u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalBound u p ⟨hp⟩ 3 _ D.r3)

/-! ## §4. G13: the newform and the common constituent -/

/-- `r` is attached to `f` outside `S`: at every arithmetic Frobenius above `p ∉ S`, the trace is
`ι_L(α)` with `ι_C(α) = a_p(f)` (`AttachedUpToTwist` with trivial twist, without the
unramifiedness clause). -/
def AttachedOutside {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (f : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ∃ α : Qbar, ιC α = coeff f p ∧
    ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
      (r.mat τ).trace = ιL α

/-- E1's hypothesis (copied from `scratch/g0-split/part_split.lean`): for some prime `ℓ` and
field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common nonzero constituent, as
`G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- **G13Out** on the data `D`: a newform `f` of weight 2, level `N ≥ 1` and nebentypus `χ`;
`r₅` is attached to `f` outside a finite set; and for every `J₁(N)` `J` over `ℚ`, `V₅(A)` and
`V₅(J_{L'})` have a common constituent (`r₅|G_{L'} ≅ ρ_{f,5}|G_{L'}`). -/
def G13Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) : Prop :=
  0 < N ∧ IsNewform f χ ∧ D.r5.IsSemisimple ∧ D.r3.IsSemisimple ∧
    (∃ S, AttachedOutside D.r5 D.ιC D.ι5 f S) ∧
    ∀ J : AbVar ℚ, IsJ1 N J → CommonConstituent A (J.baseChange L)

/-- The `J`-side of E1 for a given Shimura quotient `π : J ↠ A_f` (the proof of
`E1Sub.rhoF_subrep_JL`, for given `A_f`, `π`, `θ`). -/
theorem jSide (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    (J Af : AbVar ℚ) (π : Hom J Af) (hπ : Surjective π.hom.left) {F : Type} [Field F]
    (θ : F →+* Af.End0) (ℓ : ℕ) [Fact ℓ.Prime] (emb : F →+* PadicAlgCl ℓ)
    [FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb)]
    (L : Type) [Field L] [Algebra ℚ L] (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) :
    ∃ (U : Subrepresentation
        (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)))
      (e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] Module.Dual (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb)),
      ∀ (τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (σ : GQ),
        (∀ x, i (σ x) = τ (i x)) → ∀ u : U.toSubmodule,
          e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ u,
              U.apply_mem_toSubmodule τ u.2⟩ = rhoF ℓ Af θ emb σ (e u) := by
  obtain ⟨U0, e0, he0⟩ := E1Sub.rhoF_subrep_of_surj ℓ hS hT J Af π
    (E1Sub.vSurjOfSurjective hS hF hT J Af π ℓ hπ) θ emb
  let Ψ := (E1Sub.bcV ℓ J i).baseChange (PadicAlgCl ℓ)
  have hΨ : Function.Injective Ψ := E1Sub.bcVE_injective ℓ (PadicAlgCl ℓ) J i
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ)) :=
    { toSubmodule := U0.toSubmodule.map Ψ
      apply_mem_toSubmodule := by
        rintro τ _ ⟨u, hu, rfl⟩
        obtain ⟨σ, hσ⟩ := E1Sub.exists_res i τ
        refine ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u,
          U0.apply_mem_toSubmodule σ hu, ?_⟩
        exact E1Sub.bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u }
  let eM := Submodule.equivMapOfInjective Ψ hΨ U0.toSubmodule
  refine ⟨U, eM.symm.trans e0, fun τ σ hσ u => ?_⟩
  obtain ⟨u0, rfl⟩ := eM.surjective u
  have hmap : (⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (eM u0),
      U.apply_mem_toSubmodule τ (eM u0).2⟩ : U.toSubmodule) =
      eM ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0,
        U0.apply_mem_toSubmodule σ u0.2⟩ := by
    apply Subtype.ext
    change GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (Ψ u0) =
      Ψ (GlueI3.repBaseChange (PadicAlgCl ℓ) (J.galRep ℓ) σ u0)
    exact (E1Sub.bcVE_equivariant ℓ (PadicAlgCl ℓ) J i τ σ hσ u0).symm
  simp only [LinearEquiv.trans_apply]
  rw [hmap, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact he0 σ u0

/-- **Twist bookkeeping (proved, from T24 and T25; the computation of `C9Rhof.c9_r5`).** From
Pan-Berger's output, a newform `f` of weight 2 and level `N ∣ M m²` to which `r` is attached
outside a finite set. -/
theorem newform_of_pan (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (r : GaloisRep ℓ 2) (h : PanOutput ιC ιL r) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N ∧ IsNewform f χ ∧
      ∃ S, AttachedOutside r ιC ιL f S := by
  obtain ⟨M, χg, g, m, ψD, ψ, S, hM, hg, hm, hrg, hψ⟩ := h
  obtain ⟨χ', g', hg', hcoef⟩ := hTw M m 2 χg ψD g hM hm hg
  obtain ⟨N, χ, f, hN, hNd, hf, hcf⟩ := hNew (M * m ^ 2) 2 χ' g' (by positivity) hg'
  refine ⟨N, χ, f, hN, hf, S ∪ (M * m).primeFactors, fun p hp hpS => ?_⟩
  have hMm : M * m ≠ 0 := Nat.mul_ne_zero hM.ne' hm.ne'
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hpMm : ¬ p ∣ M * m := fun h =>
    hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hMm⟩))
  have hpMm2 : ¬ p ∣ M * m ^ 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact hpMm (dvd_mul_of_dvd_left h1 _)
    · exact hpMm (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h1) _)
  obtain ⟨-, α, hα, htrα⟩ := hrg p hp hpS1
  obtain ⟨β, hβ, hψp⟩ := hψ p hp hpS1
  refine ⟨β * α, ?_, fun v τ hv hτ => ?_⟩
  · rw [map_mul, hβ, hα, hcf p hp hpMm2, hcoef p hp hpMm]
  · rw [htrα v τ hv hτ, hψp v τ hv hτ, map_mul]

/-- **E1 on `A` for a representation attached to `f` (proved from R16, Faltings' Satz 3 and 4,
I3.M0, T18, T19).** If `r` is semisimple, attached to the newform `f` outside a finite set, and
`r|_{G_L}` is a constituent of `V_ℓ(A)`, then for every `J₁(N)` `J`, `V_ℓ(A)` and `V_ℓ(J_L)` have
a common constituent: `r|G_L ≅ ρ_{f,ι}|G_L` (C9, Brauer–Nesbitt), which is a sub of
`V_ℓ(J_L) ⊗ ℚ̄_ℓ` (E1Sub). -/
theorem commonConstituent_of_attached (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple)
    (hF : FaltingsTate) (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {L : Type} [Field L] [NumberField L] (A : AbVar L)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L) (ℓ : ℕ) [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (hA : IsConstituentOf ℓ A i r) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (f : CF N 2) (hf : IsNewform f χ) (S : Finset ℕ) (hatt : AttachedOutside r ιC ιL f S)
    (J : AbVar ℚ) (hJ : IsJ1 N J) : CommonConstituent A (J.baseChange L) := by
  obtain ⟨hfin, Af, π, θ, hπ, -, hrest⟩ := hR16 N χ f J hN hf hJ
  set emb := embOf ℓ ιC ιL (coeffField f) with hemb
  obtain ⟨h2, hfr⟩ := hrest ℓ emb
  haveI : FiniteDimensional (PadicAlgCl ℓ) (eigenFun ℓ Af θ emb) :=
    Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨-, -, ⟨φ⟩, -, -⟩ := c9_core ℓ hS hT hBN hD N hN
    (fun p => (⟨coeff f p, coeff_mem_coeffField f p⟩ : coeffField f)) Af θ emb h2
    (fun p hp hpN σ hσ => (hfr p hp hpN σ hσ).1 _ rfl) S (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (toRep r) (toRep_continuous r) (toRep_semisimple r hr) (by
      intro p hp hpS _ v τ hv hτ
      obtain ⟨α, hα, hrα⟩ := hatt p hp hpS
      rw [trace_toRep, hrα v τ hv hτ]
      exact (embOf_spec ℓ ιC ιL (coeffField f) _ α hα).symm)
  obtain ⟨eφ, heφ⟩ := equivariant_of_asModule _ _ φ
  obtain ⟨U, eR, hU, heR⟩ := hA
  obtain ⟨U', eJ, heJ⟩ := jSide hS hF hT J Af π hπ θ ℓ emb L i
  let e : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] U'.toSubmodule := (eR.trans eφ).trans eJ.symm
  refine ⟨ℓ, inferInstance, PadicAlgCl ℓ, inferInstance, inferInstance, U, U', e, hU,
    fun τ u => ?_⟩
  obtain ⟨σ, hσ⟩ := E1Sub.exists_res i τ
  have h1 : eJ ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) ((J.baseChange L).galRep ℓ) τ (e u),
      U'.apply_mem_toSubmodule τ (e u).2⟩ =
      eJ (e ⟨GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) τ u,
        U.apply_mem_toSubmodule τ u.2⟩) := by
    rw [heJ τ σ hσ (e u)]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [heR τ σ hσ u, heφ]
  exact congrArg Subtype.val (eJ.injective h1).symm

/-- **G13 (GLUE, proved from T24, T25, R16, Faltings' Satz 3 and 4, I3.M0, T18, T19).** -/
theorem g13 (hTw : PkgI4.EigenformTwist) (hNew : PkgI4.NewformOfEigenform)
    (hR16 : R16_EichlerShimuraJ1') (hS : FaltingsSemisimple) (hF : FaltingsTate)
    (hT : TateModuleFree) (hBN : GlueC10.BrauerNesbittChar0) (hD : FrobeniusDense)
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (h12 : G12Spec D) :
    ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), G13Spec D N χ f := by
  obtain ⟨hirr5, hirr3, hA5, -, hpan⟩ := h12
  obtain ⟨N, χ, f, hN, hf, S, hatt⟩ := newform_of_pan hTw hNew D.ιC D.ι5 D.r5 hpan
  have hss5 := isSemisimple_of_isIrreducible D.r5 hirr5
  refine ⟨N, χ, f, hN, hf, hss5, isSemisimple_of_isIrreducible D.r3 hirr3, ⟨S, hatt⟩,
    fun J hJ => ?_⟩
  exact commonConstituent_of_attached hR16 hS hF hT hBN hD A D.i 5 D.ιC D.ι5 D.r5 hss5 hA5 N hN
    χ f hf S hatt J hJ

/-! ## §5. G14: `r₃` and `r₅` against R14's representations of `f` -/

/-- **Brauer–Nesbitt against R14 (proved from R14, T18, T19).** A semisimple `r` attached to the
newform `f` outside a finite set is equivariantly isomorphic to R14's semisimple `ρ` attached to
`f` (in `AttachedTo` form: unramified outside `Nℓ`, traces `a_p` at every `p ∤ Nℓ`). -/
theorem iso_R14 (hR14 : PkgI4.EigenformRepExists) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (f : CF N 2) (hf : IsNewform f χ) (r : GaloisRep ℓ 2) (hr : r.IsSemisimple)
    (S : Finset ℕ) (hatt : AttachedOutside r ιC ιL f S) :
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∃ e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ),
        ∀ g v, e (toRep r g v) = toRep ρ g (e v) := by
  obtain ⟨ρ, hss, hρ⟩ := hR14 ℓ ιC ιL N 2 χ f hN (by norm_num) hf.1
  have hNℓ : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨φ⟩ := iso_of_arithFrob hBN hD (S ∪ (N * ℓ).primeFactors)
    (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (toRep r)
    (toRep ρ) (toRep_continuous r) (toRep_continuous ρ) (toRep_semisimple r hr)
    (toRep_semisimple ρ hss) (by
      intro p hp hpS v τ hv hτ
      have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
      have hpN : ¬ p ∣ N * ℓ := fun h =>
        hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h, hNℓ⟩))
      obtain ⟨α, hα, hrα⟩ := hatt p hp hpS1
      obtain ⟨-, α', hα', hρα⟩ := hρ p hp hpN
      have : α = α' := ιC.toRingHom.injective (hα.trans hα'.symm)
      rw [trace_toRep, trace_toRep, hrα v τ hv hτ, hρα v τ hv hτ, this])
  obtain ⟨e, he⟩ := equivariant_of_asModule _ _ φ
  exact ⟨ρ, hss, hρ, e, he⟩

/-- **G14Out** on the data `D` and the newform `f`: both `r₅` and `r₃` are equivariantly
isomorphic to semisimple representations attached to `f` in R14's `AttachedTo` form. -/
def G14Spec {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (f : CF N 2) : Prop :=
  (∃ ρ : GaloisRep 5 2, ρ.IsSemisimple ∧ ρ.AttachedTo D.ιC D.ι5 f ∧
      ∃ e : (Fin 2 → PadicAlgCl 5) ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5),
        ∀ g v, e (toRep D.r5 g v) = toRep ρ g (e v)) ∧
    (∃ ρ : GaloisRep 3 2, ρ.IsSemisimple ∧ ρ.AttachedTo D.ιC D.ι3 f ∧
      ∃ e : (Fin 2 → PadicAlgCl 3) ≃ₗ[PadicAlgCl 3] (Fin 2 → PadicAlgCl 3),
        ∀ g v, e (toRep D.r3 g v) = toRep ρ g (e v))

/-- **G14 (GLUE, proved from R14, T18, T19 and the AV-side Prop `G14TraceCompat`).** -/
theorem g14 (hR14 : PkgI4.EigenformRepExists) (hBN : GlueC10.BrauerNesbittChar0)
    (hD : FrobeniusDense) {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (h13 : G13Spec D N χ f)
    (hc : G14TraceCompat D) : G14Spec D N f := by
  obtain ⟨hN, hf, hss5, hss3, ⟨S, hatt⟩, -⟩ := h13
  obtain ⟨Sc, hSc⟩ := hc
  have hatt3 : AttachedOutside D.r3 D.ιC D.ι3 f (S ∪ Sc) := by
    intro p hp hpS
    have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
    have hpS2 : p ∉ Sc := fun h => hpS (Finset.mem_union_right _ h)
    obtain ⟨α, hα, hrα⟩ := hatt p hp hpS1
    exact ⟨α, hα, fun v τ hv hτ => hSc p hp hpS2 v τ hv hτ α (hrα v τ hv hτ)⟩
  exact ⟨iso_R14 hR14 hBN hD D.ιC D.ι5 N hN χ f hf D.r5 hss5 S hatt,
    iso_R14 hR14 hBN hD D.ιC D.ι3 N hN χ f hf D.r3 hss3 (S ∪ Sc) hatt3⟩

/-! ## §6. G15: the exponents of `N` -/

/-- **G15Out**: the exponents of the level, N5 L846-852 (`a_p = v_p(N)` by Carayol). -/
def G15Out (N : ℕ) (u : ℚ) : Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ (ZInQ.heightD : ℝ) → N.factorization p ≤ ZInQ.heightE0) ∧
    (∀ p : ℕ, p.Prime → (ZInQ.heightD : ℝ) < p → N.factorization p ≤ 2) ∧
    (∀ p : ℕ, p.Prime → p ∣ N → p ∈ ZInQ.Mult.S_mul ∨ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u)

/-- Carayol at one prime, transported along an equivariant equivalence (proved from R17's
adapted-level form). -/
theorem factorization_eq_condAt (hCar : LadicCond.CarayolR17) {ℓ : ℕ} [Fact ℓ.Prime]
    (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (hf : IsNewform f χ) (r : GaloisRep ℓ 2)
    (ρ : GaloisRep ℓ 2) (hss : ρ.IsSemisimple) (hρ : ρ.AttachedTo ιC ιL f)
    (e : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ))
    (he : ∀ g v, e (toRep r g v) = toRep ρ g (e v)) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (Lp : LadicCond.Fld p) (hL : LadicCond.IsAdapted Lp (r.restrictLocal p)) :
    (N.factorization p : ℚ) = LadicCond.condAt Lp (r.restrictLocal p) := by
  have hint := restrictLocal_intertwine (p := p) r ρ e he
  rw [← hCar ℓ ιC ιL N χ f ρ p hN hf hss hρ hpℓ Lp
    (isAdapted_of_intertwine _ _ e hint Lp hL)]
  exact condAt_eq_of_intertwine _ _ e hint Lp

/-- **G15 (GLUE, proved from R17 (`CarayolR17'`), the glue `SwanIndependent` and the open Prop
`G15LocalBounds`).** -/
theorem g15 (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CF N 2) (h13 : G13Spec D N χ f) (h14 : G14Spec D N f)
    (u : ℚ) (hloc : G15LocalBounds D u) : G15Out N u := by
  have hC := LadicCond.carayolR17_of_R17' hSw hCar
  obtain ⟨hN, hf, -⟩ := h13
  obtain ⟨⟨ρ5, hss5, hρ5, e5, he5⟩, ⟨ρ3, hss3, hρ3, e3, he3⟩⟩ := h14
  -- the exponent at `p` is a conductor exponent of `r₅` (`p ≠ 5`) or `r₃` (`p = 5`)
  have key : ∀ p : ℕ, ∀ hp : p.Prime, ∃ (Lp : @LadicCond.Fld p ⟨hp⟩) (c : ℚ),
      (N.factorization p : ℚ) = c ∧ ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → c ≤ (ZInQ.heightE0 : ℚ)) ∧
      ((ZInQ.heightD : ℝ) < p → c ≤ 2) ∧
      (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → c = 0) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases h5 : p = 5
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).2 h5
      exact ⟨Lp, _, factorization_eq_condAt hC D.ιC D.ι3 N hN χ f hf D.r3 ρ3 hss3 hρ3 e3 he3 p
        (by omega) Lp had, h1, h2, h3⟩
    · obtain ⟨Lp, had, h1, h2, h3⟩ := (hloc p hp).1 h5
      exact ⟨Lp, _, factorization_eq_condAt hC D.ιC D.ι5 N hN χ f hf D.r5 ρ5 hss5 hρ5 e5 he5 p
        h5 Lp had, h1, h2, h3⟩
  refine ⟨fun p hp hpR => ?_, fun p hp hpR => ?_, fun p hp hpN => ?_⟩
  · obtain ⟨Lp, c, hc, h1, -, -⟩ := key p hp
    have := h1 hpR
    rw [← hc] at this
    exact_mod_cast this
  · obtain ⟨Lp, c, hc, -, h2, -⟩ := key p hp
    have := h2 hpR
    rw [← hc] at this
    exact_mod_cast this
  · by_contra hcon
    push_neg at hcon
    obtain ⟨Lp, c, hc, -, -, h3⟩ := key p hp
    have h0 := h3 hcon.1 hcon.2
    rw [h0] at hc
    have hfac : N.factorization p = 0 := by exact_mod_cast hc
    have hpos : 0 < N.factorization p := hp.factorization_pos_of_dvd hN.ne' hpN
    omega

/-! ## §7. G16: `N ≤ Q_R M²` -/

/-- **G16 (GLUE, proved: `GlueConductor.level_le` with `R = D`, `S = S_mul`).** -/
theorem g16 (N : ℕ) (hN : 0 < N) (u : ℚ) (h15 : G15Out N u) :
    (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD *
      (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 := by
  obtain ⟨hsmall, hlarge, hout⟩ := h15
  exact GlueConductor.level_le ZInQ.Mult.S_mul u ZInQ.heightD GlueAssembly.one_le_heightD_real
    (fun p hp => by exact_mod_cast G0ModField.le_heightD_of_mem_S_mul hp) N hN.ne'
    hsmall hlarge hout

/-! ## §7b. G15's local bounds from ramification statements (proved from L8 and
`AdaptedExists`) -/

section LocalRamSec

open LadicCond
open PkgI4 (GQp)

/-- Glazer's uniform bound for the last upper break, `U₀ = 4(DG₀)²` (N5 L826-830). -/
def U0 : ℝ := 4 * ((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ) ^ 2

/-- **The ramification of `r` at `p` that D1-D4 establish (N5 L819-852).** (i) for `p ≤ R`
(`R = D`): every absolute upper ramification group `G_{ℚ_p}^t`, `t > U₀`, acts trivially;
(ii) for `p > R`: wild inertia acts trivially (tame case); (iii) for `p ∉ T = S ∪ supp M_S(u)`:
inertia acts trivially (G11, in local form). -/
def LocalRam (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, U0 < t → ∀ σ ∈ upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ wildSet, r.restrictLocal p σ = 1) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u →
      ∀ σ ∈ inertiaSet, r.restrictLocal p σ = 1)

/-- **Open part of G15, reduced (glue, D1-D4 on the actual `A`).** `LocalRam` for `r₅` at every
`p ≠ 5` and for `r₃` at `p = 5`. Proved cores over the kernel's finite-level objects: D1
(`GlueConductor.D1_genuine`, the break bound `≤ 4a²` from the different), D2
(`PkgI2.D2_fixed_of_raynaud`: wild inertia trivial on `V_ℓ(A)` after Raynaud), D3
(`GlueConductor.fourth_pow_mem`: the wild part of `β` at 2). Open: their instantiation on the
`r_ℓ` built in G8, and the transport from the finite-level filtrations to `upperAbs`. -/
def G15Ram {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ) :
    Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRam u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRam u p ⟨hp⟩ 3 _ D.r3)

variable {p : ℕ} [Fact p.Prime]

/-- `ρ|_{G_{ℚ_p}}` is continuous (`Field.absoluteGaloisGroup.map` is a continuous hom). -/
theorem restrictLocal_continuous {ℓ n : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ n) :
    Continuous (r.restrictLocal p) :=
  r.continuous_toHom.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

/-- Trivial wild inertia ⇒ `Sw_L(ρ) = 0`. -/
theorem swanAt_eq_zero_of_wild {k : Type*} [Field k] {n : ℕ} {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ wildSet, ρ σ = 1) (L : Fld p) : swanAt L ρ = 0 := by
  rw [swanAt]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [codimInv_eq_zero (fun σ hσ => h σ hσ.2)]
  simp

/-- `2(1 + U₀) ≤ E₀`. -/
theorem two_one_add_U0_le : 2 * (1 + U0) ≤ (ZInQ.heightE0 : ℝ) := by
  have hD : 0 < ZInQ.heightD := by
    rw [ZInQ.Compiler.Precision.heightD_eq]
    exact Nat.mul_pos (Nat.factorial_pos 324) (by positivity)
  have h1 : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
    Nat.mul_pos hD (by unfold ZInQ.heightG0; norm_num)
  rw [ZInQ.Compiler.Precision.heightE0_eq, U0]
  generalize ZInQ.heightD * ZInQ.heightG0 = x at h1 ⊢
  have hx : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h1
  have hx2 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := one_le_pow₀ hx
  have hc : (((10 * x ^ 2 : ℕ)) : ℝ) = 10 * (x : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow]; rfl
  rw [hc]
  linarith

/-- **G15's local bound from the ramification (GLUE, proved from L8 `SwanIntegral` and
`AdaptedExists`):** `a ≤ 2(1 + U₀) ≤ E₀` for `p ≤ R` (`LadicCond.condAt_le_of_upper`), `a ≤ 2`
for tame `p`, `a = 0` if unramified. -/
theorem localBound_of_ram (hL8 : SwanIntegral) (hAd : AdaptedExists (p := p)) (u : ℚ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ) (r : GaloisRep ℓ 2) (h : LocalRam u p r) :
    LocalBound u p r := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨Lp, hL⟩ := hAd ℓ (Ne.symm hpℓ) 2 (r.restrictLocal p) (restrictLocal_continuous r)
  refine ⟨Lp, hL, fun hpR => ?_, fun hpR => ?_, fun hS hM => ?_⟩
  · have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hb := condAt_le_of_upper hL8 ℓ hpℓ (r.restrictLocal p) (restrictLocal_continuous r) Lp
      hL U0 hU0 (h1 hpR)
    have : ((condAt Lp (r.restrictLocal p) : ℚ) : ℝ) ≤ ((ZInQ.heightE0 : ℚ) : ℝ) := by
      push_cast at hb ⊢
      linarith [two_one_add_U0_le]
    exact_mod_cast this
  · rw [condAt, swanAt_eq_zero_of_wild (h2 hpR), add_zero]
    exact_mod_cast codimInv_le (r.restrictLocal p) inertiaSet
  · exact condAt_eq_zero_of_unramified (h3 hS hM) Lp

/-- **G15's local bounds from `G15Ram` (GLUE, proved).** -/
theorem g15LocalBounds_of_ram (hL8 : SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h : G15Ram D u) : G15LocalBounds D u := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · exact localBound_of_ram hL8 (hAd p) u h5 D.r5 ((h p hp).1 h5)
  · exact localBound_of_ram hL8 (hAd p) u (by omega) D.r3 ((h p hp).2 h5)

end LocalRamSec

/-! ## §8. The range G13-G16 assembled -/

/-- **G16Out**: what G13-G16 deliver to `ModularConstituent`: a level `1 ≤ N ≤ Q_R M²` (with
`R = D`, `M = M_{S_mul}(u)`) such that `V₅(A)` and `V₅(J_{L'})` have a common constituent for
every `J₁(N)` `J` over `ℚ`. -/
def G16Out {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ) : Prop :=
  ∃ N : ℕ, 0 < N ∧
    (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
    ∀ J : AbVar ℚ, IsJ1 N J → CommonConstituent A (J.baseChange L)

/-- The literature leaves this range uses (all already in `Leaves.lean` / the kernel). -/
structure NewformLeaves : Prop where
  t24 : PkgI4.EigenformTwist
  t25 : PkgI4.NewformOfEigenform
  r14 : PkgI4.EigenformRepExists
  r16 : R16_EichlerShimuraJ1'
  r17 : LadicCond.CarayolR17'
  r9a : FaltingsSemisimple
  r9b : FaltingsTate
  m0 : TateModuleFree
  t18 : FrobeniusDense
  t19 : GlueC10.BrauerNesbittChar0

/-- **G13-G16 (GLUE, proved).** From G8-G12's output on data `D`, the two open AV-side Props
`G14TraceCompat D` and `G15LocalBounds D u` on the same data, the leaves, and the glue Prop
`SwanIndependent`: the level and the common constituent of `ModularConstituent`. -/
theorem g13_g16 (lv : NewformLeaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (D : ModData L A)
    (h12 : G12Spec D) (hc : G14TraceCompat D) (hloc : G15LocalBounds D u) : G16Out A u := by
  obtain ⟨N, χ, f, h13⟩ := g13 lv.t24 lv.t25 lv.r16 lv.r9a lv.r9b lv.m0 lv.t19 lv.t18 D h12
  have h14 := g14 lv.r14 lv.t19 lv.t18 D N χ f h13 hc
  have h15 := g15 lv.r17 hSw D N χ f h13 h14 u hloc
  exact ⟨N, h13.1, g16 N h13.1 u h15, h13.2.2.2.2.2⟩

/-- **G13-G16, reduced form (GLUE, proved).** As `g13_g16`, with G15's open part in the
ramification form `G15Ram` and the conductor arithmetic proved from the glue Props L8
(`SwanIntegral`) and `AdaptedExists` (both stated in the kernel's `LadicCond`). -/
theorem g13_g16_ram (lv : NewformLeaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (D : ModData L A)
    (h12 : G12Spec D) (hc : G14TraceCompat D) (hram : G15Ram D u) : G16Out A u :=
  g13_g16 lv hSw u D h12 hc (g15LocalBounds_of_ram hL8 hAd D u hram)

/-- With a `J₁(N)` from T33 (`JacobianExists`) and the glue target `X1ModelExists`: the `N`
of `G16Out` has a `J₁(N)`, as `ModularConstituent` asks. -/
theorem g16Out_with_J1 (hJac : JacobianExists ℚ) (hX : X1ModelExists)
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (h : G16Out A u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨N, hN, hle, hcc⟩ := h
  obtain ⟨J, hJ⟩ := exists_J1 hJac hX N hN
  exact ⟨N, J, hN, hJ, hle, hcc J hJ⟩

/-- **The G13-G16 conclusion in the shape of `ModularConstituent`'s last conjuncts** (kernel
objects): for a model `A/L'` with G8-G12's data `D` and the two open Props on `D`, there are a level
`N` with `0 < N ≤ Q_R M²`, a `J₁(N)` `J` over `ℚ` and a common constituent of `V_ℓ(A)` and
`V_ℓ(J_{L'})`. -/
theorem modularConstituent_tail (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15Ram D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, hram⟩ := h
  exact g16Out_with_J1 hJac hX u (g13_g16_ram lv hSw hL8 hAd u D h12 hc hram)

/-! ## §9. Bridge from g0-mod-galois's interface (draft at origin/wip/g0-mod-galois ad7f14c2)

The definitions `resQ`, `Vb`, `tate`, `Intertwines`, `G8Out` (here `GalG8Out`), `G12Out` (here
`GalG12Out`) are copied verbatim from
`scratch/g0-mod-galois/part_galois.lean` (namespace `G0Galois` there), over the kernel's objects. -/

section Bridge

/-- (copied from g0-mod-galois) The restriction map `G_K → G_ℚ`. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied from g0-mod-galois) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied from g0-mod-galois) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied from g0-mod-galois) `e` intertwines `f g` with `r(g) ⊕ r(g)`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- (copied from g0-mod-galois) **Output of G8.** -/
def GalG8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2) : Prop :=
  (∀ σ, ρ (resQ K σ) = tate A ℓ σ) ∧
  ∃ e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ),
    Intertwines ρ r.mat e ∧
    Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤

/-- (copied from g0-mod-galois) **Output of G12** at `ℓ = 5`: `ψ` of finite image. -/
def GalG12Out (r : GaloisRep 5 2) : Prop :=
  ∃ (N : ℕ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N 2) (ψ : GaloisChar 5)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (S : Finset ℕ),
    0 < N ∧ PkgI4.IsNormalizedEigenform g χ ∧ (Set.range ψ.toHom).Finite ∧
    r.AttachedUpToTwist ψ ιC ιL g S

/-- **Kronecker–Weber at Frobenius (GLUE, unproved; from T17 `KroneckerWeber`).** A continuous
character `ψ : G_ℚ → ℚ̄_ℓ^×` of finite image is, at arithmetic Frobenius outside a finite set,
a Dirichlet character `ψD mod m` through `ιC`, `ιL`: `ψ` factors through
`Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×` (T17), arithmetic Frobenius at `p ∤ m` maps to `p`, and the values
(roots of unity) lie in `ιL(ℚ̄)`. -/
def DirichletOfFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ψ : GaloisChar ℓ), (Set.range ψ.toHom).Finite →
    ∀ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
    ∃ (m : ℕ) (ψD : DirichletCharacter ℂ m) (S : Finset ℕ), 0 < m ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ∃ β : Qbar, ιC β = ψD (p : ZMod m) ∧
        ∀ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p → IsArithFrob τ v p →
          (ψ.toHom τ : PadicAlgCl ℓ) = ιL β

/-- **G12Out ⇒ PanOutput (GLUE, proved from `DirichletOfFinite`).** -/
theorem panOutput_of_G12Out (hDF : DirichletOfFinite) (r : GaloisRep 5 2) (h : GalG12Out r) :
    ∃ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl 5), PanOutput ιC ιL r := by
  obtain ⟨M, χ, g, ψ, ιC, ιL, S, hM, hg, hfin, hatt⟩ := h
  obtain ⟨m, ψD, S', hm, hψ⟩ := hDF 5 ψ hfin ιC ιL
  refine ⟨ιC, ιL, M, χ, g, m, ψD, ψ, S ∪ S', hM, hg, hm, fun p hp hpS => ?_,
    fun p hp hpS => hψ p hp (fun h => hpS (Finset.mem_union_right _ h))⟩
  exact hatt p hp (fun h => hpS (Finset.mem_union_left _ h))

/-- The embedding `ℚ̄ → K̄` underlying Mathlib's `Field.absoluteGaloisGroup.map`: it intertwines
`resQ K τ` with `τ`. -/
theorem resQ_spec (K : Type) [Field K] [NumberField K] :
    ∃ i : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x,
      i (resQ K τ x) = τ (i x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  refine ⟨g.toRingHom, fun τ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) τ)
    (AlgebraicClosure ℚ) x

/-- **G8Out ⇒ IsConstituentOf (GLUE, proved).** `U = ker(pr₂ ∘ e)` is the constituent. -/
theorem isConstituentOf_of_GalG8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (r : GaloisRep ℓ 2) (h : GalG8Out A ℓ ρ r)
    (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K)
    (hi : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x, i (resQ K τ x) = τ (i x)) :
    IsConstituentOf ℓ A i r := by
  obtain ⟨hres, e, he, -⟩ := h
  let W : Submodule (PadicAlgCl ℓ) (Vb A ℓ) :=
    LinearMap.ker ((LinearMap.snd (PadicAlgCl ℓ) _ _) ∘ₗ e.toLinearMap)
  have hW : ∀ v, v ∈ W ↔ (e v).2 = 0 := fun v => Iff.rfl
  have hstab : ∀ (σ : Field.absoluteGaloisGroup K) (w : Vb A ℓ), w ∈ W →
      GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ w ∈ W := by
    intro σ w hw
    rw [hW] at hw ⊢
    have h1 := he (resQ K σ) w
    rw [hres σ] at h1
    change (e (tate A ℓ σ w)).2 = 0
    rw [h1, hw, Matrix.mulVec_zero]
  let U : Subrepresentation (GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)) :=
    { toSubmodule := W
      apply_mem_toSubmodule := fun σ w hw => hstab σ w hw }
  let f : U.toSubmodule →ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    (LinearMap.fst (PadicAlgCl ℓ) _ _) ∘ₗ e.toLinearMap ∘ₗ W.subtype
  have hmemW : ∀ w : Fin 2 → PadicAlgCl ℓ, e.symm (w, 0) ∈ W := fun w => by
    rw [hW, LinearEquiv.apply_symm_apply]
  let eU : U.toSubmodule ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    { f with
      invFun := fun w => ⟨e.symm (w, 0), hmemW w⟩
      left_inv := fun u => by
        apply Subtype.ext
        change e.symm ((e u).1, 0) = u
        have hu : (e u).2 = 0 := (hW u).mp u.2
        rw [← hu, Prod.mk.eta, LinearEquiv.symm_apply_apply]
      right_inv := fun w => by
        change (e (e.symm (w, 0))).1 = w
        rw [LinearEquiv.apply_symm_apply] }
  have hσ : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (σ : GQ), (∀ x, i (σ x) = τ (i x)) →
      σ = resQ K τ := by
    intro τ σ hστ
    ext x
    apply i.toRingHom.injective
    change i (σ x) = i (resQ K τ x)
    rw [hστ, hi]
  refine ⟨U, eU, ?_, fun τ σ hστ u => ?_⟩
  · intro hbot
    have hmem : e.symm ((Pi.single 0 1 : Fin 2 → PadicAlgCl ℓ), 0) ∈ U.toSubmodule := hmemW _
    rw [hbot] at hmem
    have h0 : e.symm ((Pi.single 0 1 : Fin 2 → PadicAlgCl ℓ), 0) = 0 := hmem
    have h1 := congrArg (fun v => (e v).1 0) h0
    simp at h1
  · rw [hσ τ σ hστ]
    change (e (tate A ℓ τ u)).1 = toRep r (resQ K τ) ((e u).1)
    have h1 := he (resQ K τ) u
    rw [hres τ] at h1
    rw [h1, toRep_apply, Matrix.toLin'_apply]

/-- **G12Spec from g0-mod-galois's outputs (GLUE, proved from `DirichletOfFinite`).** Their
`G8Out` at `ℓ = 5` and `ℓ = 3` and `G12Out r₅` give `i`, `ιC`, `ι₅` such that the data
`⟨i, ιC, ι₅, ι₃, r₅, r₃⟩` satisfy `G12Spec` for **every** `ι₃` (`G12Spec` does not involve `ι₃`).
So `ι₃` can be chosen afterwards, compatibly with `ι₅`, as `G14TraceCompat` requires. -/
theorem g12Spec_of_galois (hDF : DirichletOfFinite) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (ρ5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (ρ3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2)
    (r3 : GaloisRep 3 2) (h5 : GalG8Out A 5 ρ5 r5) (h3 : GalG8Out A 3 ρ3 r3)
    (h12 : GalG12Out r5) :
    ∃ (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) (ιC : Qbar →ₐ[ℚ] ℂ)
      (ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5),
      ∀ ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3, G12Spec (⟨i, ιC, ι5, ι3, r5, r3⟩ : ModData K A) := by
  obtain ⟨i0, hi0⟩ := resQ_spec K
  let i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := i0.toRatAlgHom
  have hi : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x, i (resQ K τ x) = τ (i x) := hi0
  obtain ⟨ιC, ιL, hpan⟩ := panOutput_of_G12Out hDF r5 h12
  have hirr : ∀ {ℓ : ℕ} [Fact ℓ.Prime] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
      (r : GaloisRep ℓ 2), GalG8Out A ℓ ρ r → r.IsIrreducible := by
    intro ℓ _ ρ r h
    obtain ⟨-, -, -, hadj⟩ := h
    rw [PkgI4.GaloisRep.IsIrreducible, eq_top_iff, ← hadj]
    exact Algebra.adjoin_mono (Set.range_subset_iff.mpr fun σ => ⟨resQ K σ, rfl⟩)
  exact ⟨i, ιC, ιL, fun ι3 => ⟨hirr ρ5 r5 h5, hirr ρ3 r3 h3,
    isConstituentOf_of_GalG8Out A 5 ρ5 r5 h5 i hi, isConstituentOf_of_GalG8Out A 3 ρ3 r3 h3 i hi,
    hpan⟩⟩

end Bridge

/-! ## §10. Local unramifiedness from G11's global form (proved) -/

section LocalGlobal

open PkgI4 (GQp)
open scoped Pointwise

variable (p : ℕ) [Fact p.Prime]

/-- The embedding `ℚ̄ → ℚ̄_p` underlying `PkgI4.decomp p` (Mathlib's
`Field.absoluteGaloisGroup.map`): it intertwines `decomp p σ` with `σ`. -/
theorem decomp_spec : ∃ j : Qbar →+* PadicAlgCl p,
    ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x, j (PkgI4.decomp p σ x) = σ (j x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) := g.toAlgebra
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ)
    (AlgebraicClosure ℚ) x

/-- The valuation subring `{x ∈ ℚ̄ : ‖j x‖ ≤ 1}` of the place of `ℚ̄` above `p` given by `j`. -/
def vj (j : Qbar →+* PadicAlgCl p) : ValuationSubring Qbar :=
  (PadicAlgCl.valued p).v.valuationSubring.comap j

theorem mem_vj (j : Qbar →+* PadicAlgCl p) (x : Qbar) : x ∈ vj p j ↔ ‖j x‖ ≤ 1 := by
  rw [vj, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
  change ‖j x‖₊ ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (spectral norm). -/
theorem norm_aut (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : PadicAlgCl p) :
    ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

theorem mem_nonunits_vj (j : Qbar →+* PadicAlgCl p) (b : Qbar) (hb : ‖j b‖ < 1) :
    b ∈ (vj p j).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : b = 0
  · exact Or.inl h0
  · refine Or.inr fun hinv => ?_
    rw [mem_vj, map_inv₀, norm_inv] at hinv
    have hpos : 0 < ‖j b‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr h0)
    rw [inv_le_one₀ hpos] at hinv
    linarith

theorem liesOver_vj (j : Qbar →+* PadicAlgCl p) : LiesOver (vj p j) p := by
  apply mem_nonunits_vj
  rw [map_natCast, LadicCond.norm_p_kbar]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- **Global unramified ⇒ local inertia acts trivially (GLUE, proved).** If `r` is unramified at
`p` in PkgI4's global sense (every inertia group of `G_ℚ` at a place above `p` acts trivially),
then `r|G_{ℚ_p}` is trivial on the local inertia set `LadicCond.inertiaSet`. -/
theorem localUnram_of_unramifiedAt {ℓ n : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ n)
    (hr : r.UnramifiedAt p) : ∀ σ ∈ LadicCond.inertiaSet, r.restrictLocal p σ = 1 := by
  obtain ⟨j, hj⟩ := decomp_spec p
  intro σ hσ
  set τ := PkgI4.decomp p σ with hτ
  have hdec : τ ∈ (vj p j).decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_vj, mem_vj, AlgEquiv.smul_def,
      hτ, ← map_inv, hj, norm_aut]
  have hin : (⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) ∈
      (vj p j).inertiaSubgroup ℚ := by
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change (⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • IsLocalRing.residue _ a =
      IsLocalRing.residue _ a
    rw [← IsLocalRing.ResidueField.residue_smul]
    apply Ideal.Quotient.eq.mpr
    have hb : ((⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • a - a : vj p j) =
        ⟨τ a - a, by
          have := ((⟨τ, hdec⟩ : (vj p j).decompositionSubgroup ℚ) • a - a).2
          exact this⟩ := rfl
    have hnorm : ‖j (τ (a : Qbar) - a)‖ < 1 := by
      rw [map_sub, hτ, hj]
      exact hσ (j a) ((mem_vj p j a).mp a.2)
    obtain ⟨hmem, hmax⟩ :=
      (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp
        (mem_nonunits_vj p j _ hnorm)
    rw [hb]
    exact hmax
  exact hr (vj p j) (liesOver_vj p j) ⟨τ, hdec⟩ hin

end LocalGlobal

/-- `LocalRam` with clause (iii) in G11's global form (`G0Galois.G11Out`: `r.UnramifiedAt p`). -/
def LocalRamG (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ LadicCond.wildSet, r.restrictLocal p σ = 1) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → r.UnramifiedAt p)

/-- **Open part of G15, final form.** Clauses (i)-(ii) of `LocalRam` (D1-D4 on G8's `r_ℓ`) and
clause (iii) as G11's output (proved by g0-mod-galois as `g11`, `G0Galois.G11Out`). -/
def G15RamG {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ) :
    Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRamG u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRamG u p ⟨hp⟩ 3 _ D.r3)

theorem g15Ram_of_G {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h : G15RamG D u) : G15Ram D u := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (h p hp).1 h5
    exact ⟨h1, h2, fun hS hM => localUnram_of_unramifiedAt p D.r5 (h3 hS hM)⟩
  · obtain ⟨h1, h2, h3⟩ := (h p hp).2 h5
    exact ⟨h1, h2, fun hS hM => localUnram_of_unramifiedAt p D.r3 (h3 hS hM)⟩

/-- **G13-G16, final form (GLUE, proved).** As `modularConstituent_tail`, with G15's open part
`G15RamG` (D1-D4's ramification statements on G8's `r_ℓ`, and G11's output). -/
theorem modularConstituent_tail_G (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, hram⟩ := h
  exact modularConstituent_tail lv hJac hX hSw hL8 hAd A u ⟨D, h12, hc, g15Ram_of_G D u hram⟩

end G0ModNewform

end

end G0ModNewformSec


/-! ## g0-assemble: `AfterG7` (G8-G16) from g0-mod-galois and g0-mod-newform

`G0ModField.AfterG7` is proved from the leaf bundles, g0-mod-galois' `GaloisPieces` (with `R14Det`,
the published determinant clause of R14, as g0-mod-galois found), g0-mod-newform's leaves and glue,
and two new named glue Props on the data of G7:

* `ModelG3G6`: the outputs of G3 (inertia outside `T` acts trivially on `V_ℓ(A_{L'})`, `ℓ = 3, 5`)
  and of G5-G6 (`End(A_{L'})` a noncommutative division ring) for the model `A_{L'}` that
  g0-mod-field's `G7Data` delivers. G6 is NoCM on the fibre: **QM-PIN** (like FS5).
* `LinkedTateData`: g0-mod-field's bridge `TateBridge` at `ℓ = 5` and `ℓ = 3` **from the same
  descent datum** (the Tate functor applied to one family `m_σ = μ_σ ∘ σ`), together with
  g0-mod-newform's two AV-side Props `G14TraceCompat` and `G15RamG` for every `r₅`, `r₃` that G8
  attaches to these data. They must be stated jointly: g0-mod-newform found that `G14TraceCompat`
  is false for unrelated constituents (a twist by a character of `Gal(L'/ℚ)` changes `r_ℓ` but
  not its restriction to `G_{L'}`), and `TateBridge` alone (∀ ℓ ∃ data) does not link the data at
  3 and 5. Only clauses (i)-(ii) of `G15RamG` are asked (`G15RamWild`); clause (iii) is G11's
  output (`G0Galois.g11`), applied in `g15RamG_of_wild`.

The composition: `galoisG2Out_of_g7Data` (g0-mod-field, G2Out from G7Data) → `g8_g12_of_leaves`
at 5 and `g8_g11` at 3 (g0-mod-galois) → `g12Spec_of_galois` (g0-mod-newform; the G8 and G12
outputs are g0-mod-galois' definitions, copied verbatim there) → `modularConstituent_tail_G`
(g0-mod-newform, G13-G16). -/

section G0AssembleAfterG7Sec

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue G3 + G5-G6 on G7's model** (g0-assemble; QM-PIN for the G6 part). For every fibre
context and G7 data of g0-mod-field: `End(A_{L'})` is a noncommutative division ring
(`G0Galois.G6Out`; NoCM, N5 G6), and inertia at primes outside `T(u)` acts trivially on
`ℚ̄_ℓ ⊗ V_ℓ(A_{L'})` for `ℓ = 5, 3` (`G0Galois.G3Out`; G3, good reduction of the QM model away
from `T` with Néron–Ogg–Shafarevich R7a). -/
def ModelG3G6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G6Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 (T u) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 (T u)

/-- Clauses (i)-(ii) of g0-mod-newform's `LocalRamG` (its clause (iii) is G11's output): for
`p ≤ D`, absolute upper ramification groups above `U₀` act trivially; for `p > D`, wild inertia
acts trivially (N5 L819-852, "D1-D4 on G8's `r_ℓ`"). -/
def LocalRamWild (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : PkgI4.GaloisRep ℓ 2) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ LadicCond.wildSet, r.restrictLocal p σ = 1)

/-- g0-mod-newform's `G15RamG` without clause (iii): `LocalRamWild` for `r₅` at `p ≠ 5` and for
`r₃` at `p = 5`. -/
def G15RamWild {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : G0ModNewform.ModData L A) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRamWild p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRamWild p ⟨hp⟩ 3 _ D.r3)

/-- **`G15RamG` from its clauses (i)-(ii) and G11's output** (proved): clause (iii) at
`p ∉ S_mul`, `p ∤ M_{S_mul}(u)` is `G0Galois.G11Out (T u)`, since such `p` is not in
`T u = S_mul ∪ supp M_{S_mul}(u)`. -/
theorem g15RamG_of_wild {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : G0ModNewform.ModData L A) (u : ℚ) (hw : G15RamWild D)
    (h5 : G0Galois.G11Out (T u) D.r5) (h3 : G0Galois.G11Out (T u) D.r3) :
    G0ModNewform.G15RamG D u := by
  intro p hp
  have hT : p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → p ∉ T u := by
    intro hS hM hmem
    simp only [T, GlueDescent.ramSet, Finset.mem_union] at hmem
    rcases hmem with h | h
    · exact hS h
    · exact hM (Nat.dvd_of_mem_primeFactors h)
  refine ⟨fun h5' => ?_, fun h5' => ?_⟩
  · obtain ⟨hi, hii⟩ := (hw p hp).1 h5'
    exact ⟨hi, hii, fun hS hM => h5 p hp (hT hS hM) h5'⟩
  · obtain ⟨hi, hii⟩ := (hw p hp).2 h5'
    exact ⟨hi, hii, fun hS hM => h3 p hp (hT hS hM) (by omega)⟩

/-- **Glue: linked Tate data with G14-G15 on them** (g0-assemble; g0-mod-field's `TateBridge`
at `ℓ = 5, 3` from one descent datum, with g0-mod-newform's `G14TraceCompat` and `G15RamG`).
For every fibre context and G7 data: operator data at `ℓ = 5` and `ℓ = 3` satisfying
g0-mod-galois' `G7Out`, such that for all `r₅`, `r₃` with G8's output on these data and all
embeddings `i`, `ι_ℂ`, `ι₅`, some `ι₃` makes the traces compatible (`G14TraceCompat`, N5 L776-795)
and `r₅`, `r₃` have Glazer's wild local ramification (`G15RamWild`: clauses (i)-(ii) of
g0-mod-newform's `G15RamG`, N5 L819-852; clause (iii) is proved from G11, `g15RamG_of_wild`). -/
def LinkedTateData : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a₅ β₅ : PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a₃ β₃ : PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅ a₅ β₅ u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃ a₃ β₃ u₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ a₅ β₅) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ a₃ β₃) r₃ →
        ∀ (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L') (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
          (ι5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5), ∃ ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3,
          G0ModNewform.G14TraceCompat
            (⟨i, ιC, ι5, ι3, r₅, r₃⟩ : G0ModNewform.ModData L'
              (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) ∧
          G15RamWild
            (⟨i, ιC, ι5, ι3, r₅, r₃⟩ : G0ModNewform.ModData L'
              (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))

/-- g0-mod-newform's leaf bundle from the two leaf bundles and the concrete R17
(`LadicCond.CarayolR17'`; the bundle's `r17` is still an `opaque` placeholder). -/
theorem newformLeaves_of (r : ResearchLeaves) (t : TextbookLeaves)
    (hCar : LadicCond.CarayolR17') : G0ModNewform.NewformLeaves :=
  ⟨C9Rhof.eigenformTwist_of_hsyn t.t24, t.t25, C9Rhof.eigenformRepExists_of_hsyn r.r14, r.r16,
    hCar, r.r9a, r.r9b, t.t26, C9Rhof.frobeniusDense_of_hsyn t.frobeniusDense,
    TSkolemKW.C10.brauerNesbittChar0'⟩

/-- The two textual copies of `CommonConstituent` (g0-mod-newform's, g0-mod-field's) agree. -/
theorem commonConstituent_copy' {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) :
    G0ModNewform.CommonConstituent A J ↔ G0ModField.CommonConstituent A J := Iff.rfl

/-- **`AfterG7` (G8-G16), proved** from the leaf bundles, g0-mod-galois' `GaloisPieces`,
g0-mod-newform's `DirichletOfFinite`, the concrete R17 `CarayolR17'`, the three LadicCond glue
Props, and the two glue Props `ModelG3G6`, `LinkedTateData`. -/
theorem afterG7_of (r : ResearchLeaves) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    G0Galois.g8_g12_of_leaves r t m _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) m.deRham m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G (newformLeaves_of r t hCar) t.t33 t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩

end HSyn.G0AssembleMod

end G0AssembleAfterG7Sec

#print axioms HSyn.G0AssembleMod.afterG7_of

/-! ## Kernel copy: excerpts of ZInQKernel/HDecomp/C10/Link.lean (verbatim: lines 26-32, 81-111, 150-180, 227-233), the
declarations g14-trace's `common_trace` uses (`FrobCompare`, `trace_T_of_frobCompare`, `cast_ne_zero_of_charP`). -/
section GlueC10LinkSec
noncomputable section

open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace GlueC10Link

/-- If `E ⊗_K M` is finite over `E` then `M` is finite over `K` (fields). -/
theorem finite_of_baseChange {K E M : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup M]
    [Module K M] [Module.Finite E (E ⊗[K] M)] : Module.Finite K M := by
  let b := Module.Free.chooseBasis K M
  have : Finite (Module.Free.ChooseBasisIndex K M) :=
    Module.Finite.finite_basis (Algebra.TensorProduct.basis E b)
  exact Module.Finite.of_basis b

/-- `V_ℓ(φ)` extended to `E ⊗_{ℚ_ℓ} V_ℓ(Ā)`, for a field `E ⊇ ℚ_ℓ`. -/
abbrev endE {k : Type} [Field k] {A : AbVar k} (φ : AbVar.End A) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] : Module.End E (E ⊗[ℚ_[ℓ]] A.V ℓ) :=
  ((AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange E

/-- **The ℓ-independent trace on `V_ℓ ⊗ E`** (from Mumford §19 Thm 4). One integer `t` is the
trace of `φ` on `E ⊗ V_ℓ(A)` for every prime `ℓ ≠ char k` and every field `E ⊇ ℚ_ℓ` over which
`E ⊗ V_ℓ(A)` is finite-dimensional. -/
theorem trace_endE_indep (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k)
    (φ : AbVar.End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ)],
        LinearMap.trace E _ (endE φ ℓ E) = (t : E) := by
  obtain ⟨t, ht⟩ := PkgI3.trace_indep_of_ell hM k A φ
  refine ⟨t, fun ℓ _ hℓ E _ _ _ => ?_⟩
  have : Module.Finite ℚ_[ℓ] (A.V ℓ) := finite_of_baseChange (E := E)
  classical
  let b := Module.Free.chooseBasis ℚ_[ℓ] (A.V ℓ)
  let _ : Fintype (Module.Free.ChooseBasisIndex ℚ_[ℓ] (A.V ℓ)) := Fintype.ofFinite _
  rw [endE, LinearMap.trace_baseChange, ht ℓ hℓ _ b, map_intCast]


/-! ## 4. The descended representation over the coefficient field `C` -/
/-! ## 5. The Frobenius comparison (an input from the surface `A`) and the trace link -/

/-- **The Frobenius comparison at `ℓ` (from the surface `A`; not glue).** For `σ` a Frobenius
lift at a place `v` of good reduction with `ℓ ≠ p`, `Tσ = μ_σ ∘ σ` on `V = V_ℓ(A) ⊗ E`, `Ā = Ā_v`
over the residue field `k`, `α' = N·(μ̄_σ ∘ F) ∈ End(Ā)` (`N ≥ 1` clears the denominator of the
quasi-isogeny `μ_σ`): some `E`-linear isomorphism `Φ : V ≃ E ⊗ V_ℓ(Ā)` carries `N·Tσ` to
`V_ℓ(α')`. In the manuscript `Φ` is the reduction isomorphism (Serre–Tate), and the square
commutes by the Néron mapping property (reduction of `μ_σ`) and because `σ` acts on reduced
points as the relative `p`-Frobenius `F : Ā → Ā^{(p)} = \overline{{}^σA}` (N5 L781-786). -/
def FrobCompare (ℓ : ℕ) [Fact ℓ.Prime] {E V : Type*} [Field E] [Algebra ℚ_[ℓ] E]
    [AddCommGroup V] [Module E V] (Tσ : Module.End E V) {k : Type} [Field k] {A : AbVar k}
    (α : AbVar.End A) (N : ℕ) : Prop :=
  ∃ Φ : V ≃ₗ[E] E ⊗[ℚ_[ℓ]] A.V ℓ, Φ.conj ((N : E) • Tσ) = endE α ℓ E

/-- Under the comparison, `N · tr T(σ) = t`, the ℓ-independent trace of `α'`. -/
theorem trace_T_of_frobCompare (hM : CharPolyIndepOfEll) {k : Type} [Field k] (A : AbVar k)
    (α : AbVar.End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
        [FiniteDimensional E V] (Tσ : Module.End E V) (N : ℕ), FrobCompare ℓ Tσ α N →
        (N : E) * LinearMap.trace E V Tσ = (t : E) := by
  obtain ⟨t, ht⟩ := trace_endE_indep hM A α
  refine ⟨t, fun ℓ _ hℓ E V _ _ _ _ _ Tσ N ⟨Φ, hΦ⟩ => ?_⟩
  have : Module.Finite E (E ⊗[ℚ_[ℓ]] A.V ℓ) := Module.Finite.equiv Φ
  rw [← ht ℓ hℓ E, ← hΦ, LinearMap.trace_conj', map_smul, smul_eq_mul]

/-- **The trace link (GLUE, proved from Mumford §19 Thm 4):
`c_p = ½ · β(σ)⁻¹ a_σ · tr α_σ`.** Given `Ā` and `α' ∈ End(Ā)` there is one integer `t`
(the trace of `α'` on `V_ℓ(Ā)`, the same for every `ℓ ≠ char k`) such that for every prime
`ℓ ≠ char k`, every coefficient field `E ⊇ ℚ_ℓ` with embedding `emb : C → E`, every descent datum
`(T, c, ε, a, β)` and matrix units `u`, and every `σ` whose `T σ` satisfies the Frobenius
comparison with `α'` and `N`:

/-- `ℓ ≠ p` in a field of characteristic `p`. -/
theorem cast_ne_zero_of_charP {k : Type} [Field k] {p ℓ : ℕ} [CharP k p] (hp : p.Prime)
    (hℓ : ℓ.Prime) (hne : p ≠ ℓ) : (ℓ : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k p ℓ]
  exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h)


end GlueC10Link
end
end GlueC10LinkSec

/-! ## g14-trace copy: scratch/g14-trace/part_g14.lean, verbatim lines 26-31 (header), 110-163 (§2 and
`FrobTraceLink`), 194-293 (§4-§5); §1 (the twist obstruction), `FrobSquaresLink` and §6 are omitted. -/
section G14TraceSec
noncomputable section

namespace G14Trace

open PkgI4 (Qbar GQ LiesOver IsArithFrob GaloisRep)
open PkgI3 G0ModNewform GlueC10Link

/-! ## §2. Traces through G8's intertwining (proved) -/

/-- If `e : V ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` intertwines `f g` with `m g ⊕ m g`, then `tr f(g) = 2 tr m(g)`. -/
theorem trace_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (f : G → Module.End (PadicAlgCl ℓ) V)
    (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : Intertwines f m e) (g : G) :
    LinearMap.trace (PadicAlgCl ℓ) V (f g) = 2 * (m g).trace := by
  haveI : Module.Finite (PadicAlgCl ℓ) V := Module.Finite.equiv e.symm
  have hconj : e.conj (f g) = LinearMap.prodMap (Matrix.toLin' (m g)) (Matrix.toLin' (m g)) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h g, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, Matrix.toLin'_apply]
  rw [← LinearMap.trace_conj' (f g) e, hconj, LinearMap.trace_prodMap', Matrix.trace_toLin'_eq]
  ring

/-- One coefficient prime: if `N·tr T = t` and `tr(β⁻¹ a T) = 2 tr m` (images of
`a, β ∈ ℚ̄` under `j`), then `tr m = j(½ β⁻¹ a t/N)`. -/
theorem trace_eq_image {ℓ : ℕ} [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (T : Module.End (PadicAlgCl ℓ) V) (a β : Qbar)
    (N : ℕ) (hN : N ≠ 0) (t : ℤ) (hNT : (N : PadicAlgCl ℓ) * LinearMap.trace _ V T = t)
    (m : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (h2 : LinearMap.trace _ V (((j β)⁻¹ * j a) • T) = 2 * m.trace) :
    m.trace = j ((β)⁻¹ * a * ((t : Qbar) / N) / 2) := by
  have hNE : (N : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hT : LinearMap.trace _ V T = (t : PadicAlgCl ℓ) / N := by
    rw [eq_div_iff hNE, mul_comm, hNT]
  rw [map_smul, smul_eq_mul, hT] at h2
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_intCast, map_natCast, map_ofNat]
  linear_combination (-1 / 2 : PadicAlgCl ℓ) * h2

/-! ## §3. The AV-side glue Props -/

/-- **The Frobenius trace link (GLUE, AV side; N5 L781-786).** There is a finite set `S` of
primes such that at every arithmetic Frobenius `τ` above `p ∉ S` there are an abelian variety
`Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and `N ≠ 0` with
`FrobCompare` (kernel, `GlueC10Link`) at `ℓ = 3` and at `ℓ = 5`: some isomorphism
`ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ ⊗ V_ℓ(Ā)` carries `N·Tm_ℓ(τ)` to `V_ℓ(α')`. In N5, `S = T ∪ {3, 5}`
(`T` = bad primes of `A/L'`), `Ā` is the reduction of `A` at the place `v ∩ L'`, `α' = N·(μ̄_τ ∘ F)`
(relative `p`-Frobenius `F`, reduction `μ̄_τ` of the isogeny `μ_τ : {}^τA → A`, defined over
`L ⊆ L'` by N5 L638-640), and the
isomorphism is the Serre–Tate reduction isomorphism. It concerns the operators `Tm_ℓ` that
g0-mod-field's `TateBridge` builds from the points-level `m_σ = μ_σ ∘ σ` (one `m_σ` for all `ℓ`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
    LiesOver v p → IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-! ## §4. One algebraic number for both traces (proved from T7) -/

/-- **The common trace (GLUE, proved from T7, `FrobTraceLink` and the scalar link).** With
`ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ`, `a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and G8's intertwining of `ρ_ℓ` with
`r_ℓ ⊕ r_ℓ` at `ℓ = 3, 5`: outside a finite set, at every arithmetic Frobenius `τ`, the traces of
`r₅(τ)` and `r₃(τ)` are `j₅(x)` and `j₃(x)` for one `x = ½ β(τ)⁻¹ a(τ) tr(α')/N ∈ ℚ̄`. -/
theorem common_trace (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2) (r3 : GaloisRep 3 2)
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) r3)
    (hF : FrobTraceLink A Tm5 Tm3) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (r5.mat τ).trace = j5 x ∧ (r3.mat τ).trace = j3 x := by
  obtain ⟨S, hS⟩ := hF
  obtain ⟨-, e5, he5, -⟩ := h5
  obtain ⟨-, e3, he3, -⟩ := h3
  haveI : Module.Finite (PadicAlgCl 5) (Vb A 5) := Module.Finite.equiv e5.symm
  haveI : Module.Finite (PadicAlgCl 3) (Vb A 3) := Module.Finite.equiv e3.symm
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS1 : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hp3 : p ≠ 3 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  have hp5 : p ≠ 5 := fun h => hpS (Finset.mem_union_right _ (by simp [h]))
  obtain ⟨k, _, hk, Ab, α, N, hN, hc3, hc5⟩ := hS p hp hpS1 v τ hv hτ
  obtain ⟨t, ht⟩ := trace_T_of_frobCompare hM Ab α
  have hk3 : ((3 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp Nat.prime_three hp3
  have hk5 : ((5 : ℕ) : k) ≠ 0 := cast_ne_zero_of_charP hp (by norm_num) hp5
  have t5 := ht 5 hk5 (Tm5 τ) N hc5
  have t3 := ht 3 hk3 (Tm3 τ) N hc3
  refine ⟨(β τ)⁻¹ * a τ * ((t : Qbar) / N) / 2, ?_, ?_⟩
  · refine trace_eq_image j5 (Tm5 τ) (a τ) (β τ) N hN t t5 (r5.mat τ) ?_
    exact trace_of_intertwines _ r5.mat e5 he5 τ
  · refine trace_eq_image j3 (Tm3 τ) (a τ) (β τ) N hN t t3 (r3.mat τ) ?_
    exact trace_of_intertwines _ r3.mat e3 he3 τ

/-! ## §5. Choosing `ι₃` compatibly with Pan's `ι₅` (proved) -/

/-- Any two `ℚ`-embeddings of `ℚ̄` into a field differ by an endomorphism of `ℚ̄`:
`ι = j ∘ γ` (`ι(x)` is a root of the minimal polynomial of `x`, which splits in `j(ℚ̄)`). -/
theorem exists_comp_eq {F : Type*} [Field F] [Algebra ℚ F] (ι j : Qbar →ₐ[ℚ] F) :
    ∃ γ : Qbar →ₐ[ℚ] Qbar, ι = j.comp γ := by
  have hmem : ∀ x : Qbar, ∃ y : Qbar, j y = ι x := by
    intro x
    have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    set P := minpoly ℚ x with hP
    have hP0 : P.map (algebraMap ℚ Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ Qbar)).map (j : Qbar →+* F)).IsRoot (ι x) := by
      rw [Polynomial.map_map, j.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := (IsAlgClosed.splits (P.map (algebraMap ℚ Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose γf hγf using hmem
  have hj : Function.Injective j := j.toRingHom.injective
  refine ⟨{ toFun := γf
            map_one' := hj (by rw [hγf, map_one, map_one])
            map_mul' := fun x y => hj (by rw [hγf, map_mul, map_mul, hγf, hγf])
            map_zero' := hj (by rw [hγf, map_zero, map_zero])
            map_add' := fun x y => hj (by rw [hγf, map_add, map_add, hγf, hγf])
            commutes' := fun q => hj (by rw [hγf, AlgHom.commutes, AlgHom.commutes]) }, ?_⟩
  ext x
  exact (hγf x).symm

/-- **`G14TraceCompat` from the common trace (GLUE, proved).** If the traces of `r₅`, `r₃` at
Frobenius are `j₅(x)`, `j₃(x)`, and `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`, then `G14TraceCompat` holds for
any data with these `ι₅, ι₃, r₅, r₃`. -/
theorem g14TraceCompat_of_common {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3)
    (γ : Qbar →ₐ[ℚ] Qbar) (h5 : D.ι5 = j5.comp γ) (h3 : D.ι3 = j3.comp γ)
    (h : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p → IsArithFrob τ v p →
        ∃ x : Qbar, (D.r5.mat τ).trace = j5 x ∧ (D.r3.mat τ).trace = j3 x) :
    G14TraceCompat D := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun p hp hpS v τ hv hτ c hc => ?_⟩
  obtain ⟨x, hx5, hx3⟩ := hS p hp hpS v τ hv hτ
  have hxc : x = γ c := by
    apply j5.toRingHom.injective
    change j5 x = j5 (γ c)
    rw [← hx5, hc, h5, AlgHom.comp_apply]
  rw [hx3, hxc, h3, AlgHom.comp_apply]

/-- **G14TraceCompat on G8's construction (GLUE, proved from T7, `FrobTraceLink` and the scalar
link).** For data `D` whose `r₅`, `r₃` are G8's outputs on `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` with
`a_ℓ = j_ℓ ∘ a`, `β_ℓ = j_ℓ ∘ β`, and whose embeddings are `ι₅ = j₅ ∘ γ`, `ι₃ = j₃ ∘ γ`. -/
theorem g14TraceCompat_of_link (hM : CharPolyIndepOfEll) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} (D : ModData K A) (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (γ : Qbar →ₐ[ℚ] Qbar) (hι5 : D.ι5 = j5.comp γ)
    (hι3 : D.ι3 = j3.comp γ) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) D.r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) D.r3)
    (hF : FrobTraceLink A Tm5 Tm3) : G14TraceCompat D :=
  g14TraceCompat_of_common D j5 j3 γ hι5 hι3
    (common_trace hM A j5 j3 a β Tm5 Tm3 D.r5 D.r3 h5 h3 hF)

end G14Trace
end
end G14TraceSec

/-! ## linked-tate: g0-assemble's joint glue Props `ModelG3G6` and `LinkedTateData`, reduced

Task linked-tate (2026-11-13). Both Props are g0-assemble's (`scratch/g0-assemble/parts/87_afterg7.lean`,
copied verbatim above with `LocalRamWild`, `G15RamWild`, `g15RamG_of_wild`, `afterG7_of`). Nothing
in them is changed. Over the pin-applied `Leaves.lean` (`R1fpProps` with `R1famProps`,
`R1univProps`).

* `ModelG3G6` is proved (`modelG3G6_of`) from
  - `HSyn.G0Split.FibreSimple` (an existing `GluePieces` field, G5-G6 on any number-field model of
    the fibre; g0-fibresimple reduced it to leaves, FS1b and FS5), for the `EndDivision` half of
    `G6Out`;
  - the new named glue Prop `QMModelG3` (G3: inertia at `p ∉ {3, ℓ}` acts trivially on
    `ℚ̄_ℓ ⊗ V_ℓ` of a base change of a `QML3` object), for the two `G3Out`;
  - and a proof (no input) of the noncommutativity half of `G6Out`: the QM structure `ι` of the
    `QML3` object and base change on endomorphisms are injective ring maps, and `𝒪` is not
    commutative (`oI_oH_ne`).
* `LinkedTateData` is proved (`linkedTateData_of`) from the leaf T7 (`PkgI3.CharPolyIndepOfEll`,
  Mumford §19 Thm 4; `TextbookLeaves.t7`) and the new named glue Prop `LinkedTateCore`:
  `G7Out` data at `ℓ = 5` and `ℓ = 3` whose scalars are the images `j_ℓ ∘ a`, `j_ℓ ∘ β` of one pair
  `a, β : G_ℚ → ℚ̄` (the scalar link), with g14-trace's `FrobTraceLink` for the two operator
  families and the wild-ramification clauses for the descended operators `ρ_ℓ` themselves
  (`RhoRamWild`). `G14TraceCompat` is then g14-trace's `g14TraceCompat_of_link` (T7), and
  `G15RamWild` for every `r_ℓ` with G8's output is transported from `ρ_ℓ` through G8's
  intertwiner (`localRamWild_of_rho`).
-/

section LinkedTateSec

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry
open G0ModField

/-! ### §1 Base change on endomorphisms (copied from `scratch/bp-qmmoduli/QMAbVar.lean` L533-575:
`endBC` as unram-tate copied it, `specMap_flat`, `specMap_surjective`, `endBC_injective`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from bp-qmmoduli's `endBC`):
`End_K(A) → End_L(A_L)`, `f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism
(functoriality, and `Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

/-- `Spec L → Spec K` is flat, surjective and quasi-compact, so `Over.pullback` along it is
faithful (Mathlib, `Morphisms/FlatDescent.lean`). -/
instance specMap_flat (L : Type) [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance specMap_surjective (L : Type) [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- Base change on endomorphisms is injective. -/
theorem endBC_injective (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    Function.Injective (endBC A L) := by
  intro f g h
  apply PkgI3.AbVar.Hom.ext'
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective
    (congrArg PkgI3.AbVar.Hom.hom h)

end BaseChangeEnd

/-! ### §2 The noncommutativity half of `G6Out` (proved) -/

/-- `i = ofInt ![0,1,0,0] ∈ 𝒪`. -/
def oI : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩

/-- `(1 + j)/2 = ofInt ![0,0,1,0] ∈ 𝒪`. -/
def oH : LeafQM.O := ⟨LeafQM.ofInt ![0, 0, 1, 0], ⟨_, rfl⟩⟩

/-- `𝒪` is not commutative: `i · (1+j)/2 = (i+k)/2 ≠ (i−k)/2 = (1+j)/2 · i`. -/
theorem oI_oH_ne : oI * oH ≠ oH * oI := by
  intro h
  have h1 : ((oI * oH : LeafQM.O) : LeafQM.B) =
      LeafQM.ofInt (LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0]) := LeafQM.ofInt_mul _ _
  have h2 : ((oH * oI : LeafQM.O) : LeafQM.B) =
      LeafQM.ofInt (LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0]) := LeafQM.ofInt_mul _ _
  have h0 : ((oI * oH : LeafQM.O) : LeafQM.B) = ((oH * oI : LeafQM.O) : LeafQM.B) :=
    congrArg Subtype.val h
  rw [h1, h2] at h0
  have h3 := congrArg QuaternionAlgebra.imK h0
  have e1 : LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0] 3 = 1 := by decide
  have e2 : LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0] 3 = -1 := by decide
  have h4 : ((LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0] 3 : ℤ) : ℚ) / 2 =
      ((LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0] 3 : ℤ) : ℚ) / 2 := h3
  rw [e1, e2] at h4
  norm_num at h4

/-- **`End` of a twice base-changed `QML3` surface is not commutative** (proved): the images of
`i` and `(1+j)/2` under `endBC ∘ endBC ∘ ι` do not commute (both base changes and `ι` are
injective ring maps). -/
theorem noncomm_baseChange2 {K : Type} [Field K] (PK : LeafQM.AV.QML3 K) (L : Type) [Field L] [Algebra K L]
    (L' : Type) [Field L'] [Algebra L L'] :
    ∃ x y : PkgI3.AbVar.End ((PK.A.baseChange L).baseChange L'), x * y ≠ y * x := by
  let f := (endBC (PK.A.baseChange L) L').comp ((endBC PK.A L).comp PK.q.iota)
  have hf : Function.Injective f :=
    (endBC_injective _ L').comp ((endBC_injective _ L).comp PK.q.injective)
  refine ⟨f oI, f oH, fun h => oI_oH_ne (hf ?_)⟩
  rw [map_mul, map_mul]
  exact h

/-! ### §3 The `EndDivision` half of `G6Out`, from `FibreSimple` (proved) -/

/-- **`EndDivision` for every number-field model of the fibre, from the glue piece
`FibreSimple`** (proved): a model `A'/L'` of `P`'s surface (`IsModelOver`) at a fibre context
gives `FibreOver` for `(abVarEquiv L').symm A'` with the inclusion `L' ⊆ ℚ̄`. -/
theorem endDivision_of_fibreSimple (hFS : HSyn.G0Split.FibreSimple)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y} {π : LeafQM.AV.ToP1 Y.left} {u : ℚ}
    {P : LeafQM.AV.QML3 Qbar} (hctx : FibreCtx Y Φ π u P) (L' : IF) [FiniteDimensional ℚ L']
    (A' : PkgI3.AbVar L') (hA' : IsModelOver L' A' P) : PkgI3.EndDivision A' := by
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  haveI : NumberField L' := numberField_of_fd L'
  exact hFS Y Φ π h1 h2 u hu ⟨L'⟩ ((LeafAdopt.abVarEquiv L').symm A')
    ⟨algebraMap L' Qbar, y, P, hy, hπ, hA'⟩

/-! ### §4 G3 on the model: the named glue Prop `QMModelG3` -/

/-- **Glue G3 on base changes of `QML3` objects** (linked-tate; G3 = Lemma PR(ii), h-decomposition
§3 G3, with R7a; N5 L524-529 and h-trust A6, C6). For a `QML3` object `PK` over `K ⊆ ℚ̄` and a
tower `K ≤ L ≤ L'` with `L'/ℚ` finite, every inertia element of `G_{L'}` at a place above a prime
`p ∉ {3, ℓ}` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ((PK.A)_{L,L'})` (`G0Galois.G3Out … ℓ {3}`). Route
(STANDARD; the Lean parts SPECULATIVE): `PK.A` has good reduction at every DVR with `3` a unit
(`LeafQM.AV.QML3.goodReduction`, proved in `Leaves.lean` from NOS, Raynaud and
`TorsionStructure`), good reduction is preserved by base change, and Néron–Ogg–Shafarevich
(R7a, (a) ⇒ (b), `PkgI2.inertiaTrivial_of_goodReduction`) makes inertia trivial on `A[ℓⁿ]`; the
open part is the transport from PkgI2's points and valuation rings of `\bar{L'}` to `ℚ̄_ℓ ⊗ V_ℓ`
and to places of `ℚ̄` (`resQ`). GLUE. -/
def QMModelG3 : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K)
    (ℓ : ℕ) [Fact ℓ.Prime],
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ {3}

/-- `3 ∈ T(u)` (`3 ∈ S_mul`). -/
theorem three_mem_T (u : ℚ) : 3 ∈ T u :=
  Finset.mem_union_left _ (ZInQ.Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- `G3Out` is monotone in `T`. -/
theorem g3Out_mono {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ}
    [Fact ℓ.Prime] {T₁ T₂ : Finset ℕ} (hT : T₁ ⊆ T₂) (h : G0Galois.G3Out A ℓ T₁) :
    G0Galois.G3Out A ℓ T₂ :=
  fun p hp hpT hpl v hv σ' hσ => h p hp (fun h' => hpT (hT h')) hpl v hv σ' hσ

/-- **`ModelG3G6`, proved** from the glue pieces `FibreSimple` (EndDivision) and `QMModelG3`
(G3); the noncommutativity of `End(A_{L'})` is proved (`noncomm_baseChange2`). -/
theorem modelG3G6_of (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) :
    HSyn.G0AssembleMod.ModelG3G6 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  have hT : ({3} : Finset ℕ) ⊆ T u := Finset.singleton_subset_iff.mpr (three_mem_T u)
  refine ⟨⟨endDivision_of_fibreSimple hFS hctx L' _ hmod, ?_⟩, ?_, ?_⟩
  · exact @noncomm_baseChange2 K _ PK L _ (incAlg hKL) L' _ (incAlg hLL')
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 5)
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 3)

/-! ### §5 `G15RamWild` from the descended operators (proved) -/

/-- **Glazer's wild-ramification clauses (i)-(ii) for an operator family `ρ` on `V`** (the form of
`LocalRamWild` on the descended `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` instead of on G8's `r_ℓ`; N5 L819-852,
D1-D4): for `p ≤ D` the absolute upper ramification groups `G_{ℚ_p}^t`, `t > U₀`, act trivially
through `decomp p`; for `p > D` wild inertia does. -/
def RhoRamWild (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, ρ (PkgI4.decomp p σ) = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
      ρ (PkgI4.decomp p σ) = 1)

/-- If `e` intertwines `ρ` with `r ⊕ r` and `ρ(g) = 1`, then `r(g) = 1` (proved). -/
theorem toHom_eq_one_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V)
    (r : PkgI4.GaloisRep ℓ 2)
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : G0Galois.Intertwines ρ r.mat e) (g : PkgI4.GQ) (hg : ρ g = 1) : r.toHom g = 1 := by
  have hmv : ∀ x : Fin 2 → PadicAlgCl ℓ, (r.mat g).mulVec x = x := by
    intro x
    have hx := h g (e.symm (x, 0))
    rw [hg] at hx
    change e (e.symm (x, 0)) = _ at hx
    rw [LinearEquiv.apply_symm_apply] at hx
    exact (congrArg Prod.fst hx).symm
  apply Units.ext
  rw [Units.val_one]
  change r.mat g = 1
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, hmv x, Matrix.toLin'_one, LinearMap.id_apply]

/-- **`LocalRamWild` for `r` from `RhoRamWild` for `ρ`** (proved), when G8's `e` intertwines `ρ`
with `r ⊕ r`. -/
theorem localRamWild_of_rho (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V)
    (r : PkgI4.GaloisRep ℓ 2)
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : G0Galois.Intertwines ρ r.mat e) (hR : RhoRamWild p hp ρ) :
    @HSyn.G0AssembleMod.LocalRamWild p ⟨hp⟩ ℓ _ r := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun hp' t ht σ hσ => ?_, fun hp' σ hσ => ?_⟩
  · exact toHom_eq_one_of_intertwines ρ r e h _ (hR.1 hp' t ht σ hσ)
  · exact toHom_eq_one_of_intertwines ρ r e h _ (hR.2 hp' σ hσ)

/-! ### §6 `LinkedTateData` from T7 and the named glue Prop `LinkedTateCore` -/

/-- **Glue: linked Tate data on G7's model, at the level of the descended operators**
(linked-tate; the content of g0-assemble's `LinkedTateData` minus what is proved here). For every
fibre context and G7 data: one pair of scalar functions `a, β : G_ℚ → ℚ̄` and embeddings
`j₅ : ℚ̄ → ℚ̄₅`, `j₃ : ℚ̄ → ℚ̄₃` (N5 L719-722: the scalars `a_σ = deg(μ_σ)^{-1/4}`, `β_σ` lie in one
number field and are mapped to `ℚ̄_ℓ` by embeddings), and operator data at `ℓ = 5` and `ℓ = 3`
with
* g0-mod-galois' `G7Out` at each `ℓ` for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β` (the Tate functor applied
  to one family `m_σ = μ_σ ∘ σ`; g0-mod-field's `TateBridge`, which unram-tate proved for each `ℓ`
  separately from I3.M0, plus `dim A_{L'} = 2` and `rank_ℤ End(A_{L'}) = 4`);
* g14-trace's `FrobTraceLink` for the two operator families (N5 L777-786: reduction at a
  Frobenius, the relative Frobenius composed with `μ̄_τ`);
* Glazer's wild-ramification clauses (i)-(ii) for the descended operators `ρ₅` at `p ≠ 5` and
  `ρ₃` at `p = 5` (`RhoRamWild`; N5 L819-852, D1-D4).
GLUE. -/
def LinkedTateCore : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (a b : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (a g)) (fun g => j5 (b g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (a g)) (fun g => j3 (b g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₅ (fun g => j5 (a g)) (fun g => j5 (b g)))) ∧
        (p = 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₃ (fun g => j3 (a g)) (fun g => j3 (b g))))

/-- **`LinkedTateData`, proved** from the leaf T7 (`PkgI3.CharPolyIndepOfEll`) and the glue Prop
`LinkedTateCore`: for G8's `r₅`, `r₃` on the linked data and any `ι₅ = j₅ ∘ γ` (`exists_comp_eq`),
`ι₃ := j₃ ∘ γ` makes the traces compatible (g14-trace's `g14TraceCompat_of_link`), and
`G15RamWild` holds because G8's intertwiner carries `RhoRamWild` from `ρ_ℓ` to `r_ℓ`. -/
theorem linkedTateData_of (hM : PkgI3.CharPolyIndepOfEll) (hC : LinkedTateCore) :
    HSyn.G0AssembleMod.LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨a, b, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h5, h3, hF, hR⟩ :=
    hC Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  refine ⟨Tm₅, c₅, ε₅, fun g => j5 (a g), fun g => j5 (b g), u₅,
    Tm₃, c₃, ε₃, fun g => j3 (a g), fun g => j3 (b g), u₃, h5, h3, ?_⟩
  intro r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨γ, hγ⟩ := G14Trace.exists_comp_eq ι5 j5
  refine ⟨j3.comp γ, ?_, ?_⟩
  · exact G14Trace.g14TraceCompat_of_link hM ⟨i, ιC, ι5, j3.comp γ, r₅, r₃⟩ j5 j3 γ hγ rfl a b
      Tm₅ Tm₃ h8₅ h8₃ hF
  · obtain ⟨-, e5, he5, -⟩ := h8₅
    obtain ⟨-, e3, he3, -⟩ := h8₃
    intro p hp
    exact ⟨fun h => localRamWild_of_rho p hp _ r₅ e5 he5 ((hR p hp).1 h),
      fun h => localRamWild_of_rho p hp _ r₃ e3 he3 ((hR p hp).2 h)⟩

/-! ### §7 `AfterG7` with the two joint Props replaced (proved) -/

/-- **`AfterG7` (G8-G16)** from g0-assemble's inputs of `afterG7_of` with `ModelG3G6` replaced by
`FibreSimple` and `QMModelG3`, and `LinkedTateData` by `LinkedTateCore` (T7 is `t.t7`). -/
theorem afterG7_of_linked (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) (hC : LinkedTateCore) : AfterG7 :=
  HSyn.G0AssembleMod.afterG7_of r t m hDF hCar hSw hL8 hAd (modelG3G6_of hFS hG3)
    (linkedTateData_of t.t7 hC)

end HSyn.LinkedTate

end

end LinkedTateSec

#print axioms HSyn.LinkedTate.oI_oH_ne
#print axioms HSyn.LinkedTate.noncomm_baseChange2
#print axioms HSyn.LinkedTate.endDivision_of_fibreSimple
#print axioms HSyn.LinkedTate.modelG3G6_of
#print axioms HSyn.LinkedTate.toHom_eq_one_of_intertwines
#print axioms HSyn.LinkedTate.localRamWild_of_rho
#print axioms HSyn.LinkedTate.linkedTateData_of
#print axioms HSyn.LinkedTate.afterG7_of_linked

