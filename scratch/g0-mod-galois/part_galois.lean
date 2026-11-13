
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
scalar-descent data `T_σ = a_σ μ_σ ∘ σ`, `β`, and the matrix units of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`).
The coefficient field is `ℚ̄_ℓ = PadicAlgCl ℓ` throughout (Pan's coefficients). The remaining
unproved glue is named: `G8Matrix` (linear algebra), `G9Glue`, `G10Glue`, `G12Weight`, `G12Det`.
Proved here: G8 from `G7Out`, C2 and `G8Matrix`; G11 from `G2Out`, `G3Out` and G8's output, with
no further glue; G12 from Pan∘Berger (R11+R12), `weight_match`, `twist_finite` and the two named
G12 pieces. -/

section G0GaloisSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-! ### Objects -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

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
operators `Tm σ = a_σ μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` with the cocycle `c` (`Tm g Tm h = c(g,h) Tm(gh)`),
the scalars `a` and the cochain `β` with `a_g a_h c(g,h) = ε(g,h) a_{gh}` and
`β_g β_h = ε(g,h) β_{gh}` (`∂β = ε`, B2-B3), all trivial on `G_{L'}` where `Tm` is the Tate
action (`L'` is the kernel field of `β|G_L`); a system of `2 × 2` matrix units (the image of
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
`G_ℚ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` (`dim A = 2`) commuting with a system of `2 × 2` matrix units `u`,
weakly continuous, such that `r_W := ρ|_{W}` on `W = e₀₀(ℚ̄_ℓ ⊗ V_ℓ(A))` is absolutely irreducible
on `G_K` (C2's conclusion: irreducible after every field extension). Then a basis of `W`
(`dim W = 2`, `GlueDescent.MatrixUnits2.finrank_W` with `TateModuleFree`) turns `r_W` into a
continuous `r : G_ℚ → GL₂(ℚ̄_ℓ)`, `splitEquiv` composed with that basis intertwines `ρ` with
`r ⊕ r`, and Burnside's theorem over the algebraically closed `ℚ̄_ℓ` (from Mathlib's
`jacobson_density`) gives that `r(G_K)` spans `M₂(ℚ̄_ℓ)`. No arithmetic input. -/
def G8Matrix : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : Representation (PadicAlgCl ℓ) PkgI4.GQ (Vb A ℓ))
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ))
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)),
    A.dim = 2 →
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
is a quaternion algebra over `ℚ`, indefinite by Albert), and `r : G_ℚ → GL₂(ℚ̄_ℓ)` with
`ℚ̄_ℓ ⊗ V_ℓ(A) ≅ r|G_K ⊕ r|G_K`, then `r` is odd. Argument (SPECULATIVE as a reduction, each step
STANDARD): (1) N5 L742-751 shows that the descended extension `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` (built from the
quasi-isogenies `μ_σ : σA → A`, which exist by Faltings since `V_ℓ(σA) ≅ V_ℓ(A)`) has
`det r_ℓ(c) = −1`, by the Betti involution exchanging the Hodge summands; (2) any two
extensions `r, r'` of the absolutely irreducible `r|G_K` with `G_K` normal differ by a character
`θ` of `G_ℚ/G_K` (Schur), so `det r'(c) = θ(c)² det r(c) = det r(c)` since `c² = 1`. -/
def G10Glue : Prop :=
  T11_RiemannGAGA → T12_ArtinComparison → PkgI3.FaltingsTate →
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
are `{n, n + 1 − k}` for an integer `n` (the Hodge–Tate weight of `ψ|G_{ℚ₅}`). Argument:
`r ≅ ρ_g ⊗ ψ` (traces agree on a dense set, both semisimple); for `k ≥ 2` the weights of
`ρ_g ⊗ ψ` are `{0,1−k} + n`; for `k = 1`, `ρ_g` has finite image, hence weights `{0, 0}`, so
`r` would have equal weights, contradicting `{0, −1}` (so the hypotheses are inconsistent). -/
def G12Weight : Prop :=
  PkgI4.EigenformRepExists → PkgI4.EigenformHT → PkgI4.DeligneSerreFinite →
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
`H` (`G_F`, `F ⊇ K` Galois with a polarization over `F`) with `det r = ε · χ_cyc · ψ²`
(`det ρ_g = ε χ_cyc` at `k = 2`, the determinant clause of R14 as published) and
`(det r)² = χ_cyc²` on `H` (T9: `det V₅(A) = χ_cyc²` on `G_F`, with `V₅(A) ≅ r ⊕ r`). The
group theory that turns this into the finiteness of `ψ` is `GlueAssembly.twist_finite`
(proved). -/
def G12Det : Prop :=
  PkgI4.EigenformRepExists → LeafPush.T09_WeilPairing.{0} →
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
    rw [GlueDescent.rho_eq_act Tm (fun _ => 1) a β 1 this.1 this.2.1 this.2.2]
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
  have h4T : Module.finrank ℤ_[ℓ] (A.T ℓ) = 4 := by
    rw [hdim] at hrk
    have h' : ((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ∞) : WithBot ℕ∞) = ((4 : ℕ) : ℕ∞) := by
      rw [hrk]; rfl
    exact_mod_cast h'
  have h4 : Module.finrank (PadicAlgCl ℓ) (Vb A ℓ) = 4 := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, h4T]
  haveI hVne : Nontrivial (Vb A ℓ) := Module.nontrivial_of_finrank_pos (by omega)
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
  obtain ⟨r, e, hint, hadj⟩ := hM K A ℓ ρ u hc hdim (fun f v => by simpa [hρ] using hcont f v)
    hirr
  exact ⟨r, hρres, e, hint, hadj⟩

end G0Galois

end

end G0GaloisSec
