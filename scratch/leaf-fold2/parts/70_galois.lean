-- (leaf-fold2: copied from scratch/g0-assemble2/parts/70_galois.lean; 0 HDec name-resolution edits)

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

-- (leaf-fold2) `G0Galois.resQ` deleted: Leaves.lean (leaf-fold) declares it with the same body.

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

-- (leaf-fold2) `G0Galois.Vb` deleted: Leaves.lean (leaf-fold) declares it with the same body.

-- (leaf-fold2) `G0Galois.tate` deleted: Leaves.lean (leaf-fold) declares it with the same body.

/-- The restriction of a representation to an invariant subspace. -/
def restrictRep {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (W : Submodule k V) (h : ∀ g, ∀ w ∈ W, ρ g w ∈ W) :
    Representation k G W where
  toFun g := (ρ g).restrict (h g)
  map_one' := by ext w; simp
  map_mul' g g' := by ext w; simp

-- (leaf-fold2) `G0Galois.Intertwines` deleted: Leaves.lean (leaf-fold) declares it with the same body.

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

-- (leaf-fold2) `G0Galois.G10Out` deleted: Leaves.lean (leaf-fold) declares it with the same body.

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

-- (leaf-fold2) `G0Galois.toRingEquivQ` deleted: Leaves.lean (leaf-fold) declares it with the same body.

-- (leaf-fold2) `G0Galois.cycQ` deleted: Leaves.lean (leaf-fold) declares it with the same body.

-- (leaf-fold2) `G0Galois.R14Det` deleted: Leaves.lean (leaf-fold) declares it with the same body.

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

