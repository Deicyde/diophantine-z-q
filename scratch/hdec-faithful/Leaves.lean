import Mathlib
import ZInQKernel.Hypotheses.JHeight

/-!
# Theorem 4.1 (instance `SixContactMin`) decomposed into literature leaves and glue

Draft for `docs/research/hdec-faithful.md` (task hdec-faithful, 2026-11-11). Check with
`lake env lean scratch/hdec-faithful/Leaves.lean`.

* §0 builds cheap, concrete definitions on Mathlib: the absolute Galois group of `ℚ`, places of
  `ℚ̄` above `p` (valuation subrings), inertia and arithmetic Frobenius, continuous
  representations into `GL_n(ℚ̄_ℓ)` (`PadicAlgCl ℓ`), cusp forms on `Γ₁(N)` with nebentypus, and
  normalized eigenforms through the Hecke recursion of their q-expansion coefficients.
* §1 states, over those definitions, the eight leaf statements that can be stated today
  (note §3: L14, L15(a), L17, L18, L19, L27(a), L27(b), L28(a)). None is proved here.
* §2 lists the other leaves as placeholders `def … : Prop := sorry`. Their docstrings give the
  statement and the missing definition. **A placeholder has no content** (it is `sorryAx Prop`):
  these are names, not hypotheses anyone should accept.
* §3 proves two small glue facts and states the top-level glue theorem G0 with `sorry`, routed
  through the Lean proof of step F4 (`ZInQ.JHeight.sixContactMin_of_jHeightBound`).
-/

noncomputable section

namespace HDec

open scoped MatrixGroups ModularForm

/-! ## §0. Cheap definitions -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. (Its restriction to `ℚ` is then `ℤ_(p)`.) -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`: it stabilizes `v` and acts as
`x ↦ x^p` on its residue field. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (Mathlib's normed
`PadicAlgCl ℓ`). Continuity for the norm topology is equivalent to the usual notion (the image
lies in `GL_n` of a finite extension of `ℚ_ℓ`), by compactness and Baire. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- Every arithmetic Frobenius above `p` has trace `a` (meaningful at unramified `p`). -/
def GaloisRep.FrobTrace (ρ : GaloisRep ℓ n) (p : ℕ) (a : PadicAlgCl ℓ) : Prop :=
  ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
    Matrix.trace (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = a

/-- `c` is a complex conjugation: it is induced by `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c`. -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → Matrix.det (ρ.toHom c : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = -1

/-- `ρ` is (absolutely) irreducible, in Burnside's form: its image spans `M_n(ℚ̄_ℓ)`. Over the
algebraically closed `ℚ̄_ℓ` this is equivalent to irreducibility. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ)
    (Set.range fun σ => (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W) →
    ∃ W', IsCompl W W' ∧
      ∀ σ, W'.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W'

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators with nebentypus `χ`, expressed through
its coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}` (with `χ(d) = 0`
for `(d, N) > 1`). For a form with nebentypus `χ` this is equivalent to the Hecke definition
(Diamond–Shurman, Prop. 5.3.1; locator UNVERIFIED). -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `ρ` is attached to the eigenform `g` (through embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`): for
`p ∤ Nℓ`, `ρ` is unramified at `p` and its Frobenius trace is `ιL(α)` where `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧ ρ.FrobTrace p (ιL α)

/-! ## §1. Leaves statable today (not proved here) -/

/-- **L14. Skolem–Noether** (Reiner, *Maximal orders*, Thm 7.21; Tau Ceti `skolemNoether`).
Exact. -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

/-- **L15(a). Hasse principle for `Br(ℚ)`, in the form used** (Albert–Brauer–Hasse–Noether with
the sum formula; Milne, *Arithmetic duality theorems*, Ch. I). A central simple `ℚ`-algebra that
splits over every `ℚ_p` splits over `ℚ`. Consequence (the real invariant is forced to 0). -/
def HasseBrauerQ : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℚ A] [Algebra.IsCentral ℚ A] [IsSimpleRing A]
    [FiniteDimensional ℚ A] (n : ℕ), Module.finrank ℚ A = n ^ 2 →
    (∀ p : ℕ, ∀ _ : Fact p.Prime,
      Nonempty (TensorProduct ℚ ℚ_[p] A ≃ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p])) →
    Nonempty (A ≃ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ)

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Exact. -/
def KroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- **L19. Brauer–Nesbitt** (Curtis–Reiner §30). Semisimple representations of a group over a
field of characteristic 0 with equal traces are isomorphic. Exact. -/
def BrauerNesbitt : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

/-- **L27(a). Galois representations of eigenforms** (Eichler–Shimura `k = 2`, Deligne 1971
`k ≥ 2`, Deligne–Serre 1974 `k = 1`). Consequence (the published statements also give the
determinant). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **L27(b). Deligne–Serre, in the form used** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with L18 and
L19). A semisimple representation attached to a weight-one eigenform has finite image.
Consequence. -/
def DeligneSerreConseq : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **L28(a). Twisting an eigenform** (Shimura 1971, Prop. 3.64; Atkin–Li 1978). The twist of a
normalized eigenform of level `N` by a character mod `m` is a normalized eigenform of level
`Nm²` with coefficients `ψ(p) a_p` at `p ∤ Nm`. Consequence. -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p

/-! ## §2. Leaves that need new definitions: placeholders (no content)

Each docstring gives the statement (note §3), the reference, and the missing definition with
its cost tier. -/

/-- **L1** (P1). Canonical model and moduli interpretation of the level-3 QM curve `Y₃/ℚ` of
discriminant 6 (Shimura 1967 Main Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8,
§§4.8-4.17, §3; Kottwitz 1992 §5): representability of `(A, ι, λ, η)`, complex uniformization,
Hecke action of the normalizer over `ℚ`, Shimura reciprocity at CM points. Missing: abelian
schemes, QM moduli functors (very large). -/
def L01_ShimuraDeligne : Prop := sorry

/-- **L2** (P1). Baba–Granath 2008 Thm 2.1, Lemma 3.1: `X₆/W ≅ P¹_j`, branch values
`0, ∞, −16/27` with indices 4, 6, 2 at CM discriminants −4, −3, −24; `V_ℤ = V/W`. Missing: `X₆`
(very large, via L1). -/
def L02_BabaGranath : Prop := sorry

/-- **L3** (P1). Lin–Yang 2020 Ex. 30, eqs. (13)-(14): Igusa invariants
`[12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]` on the QM locus; divisors of `ψ₄`, `χ₁₀`. Missing:
the QM locus (very large), Siegel modular forms (large). -/
def L03_LinYang : Prop := sorry

/-- **L4** (P1). Igusa 1967: `ψ₄ = 2⁻² Σ θ_m⁸`, `χ₁₀ = −2⁻¹⁴ Π θ_m²` (even `m`). Missing: theta
constants with characteristics on `𝔥₂`, Siegel modular forms (large). -/
def L04_Igusa : Prop := sorry

/-- **L5** (P1). González–Rotger 2006 Thm 5.12, Prop. 5.6 (`(f,6) = 1`): fields of definition
and number of CM points on `X₆`. Missing: as L2. -/
def L05_GonzalezRotger : Prop := sorry

/-- **L6** (P2). Zariski–Nagata purity, SGA 1 X 3.1 (Stacks 0BMB). Missing: purity statement
over regular schemes (medium). -/
def L06_Purity : Prop := sorry

/-- **L7** (P2). Abhyankar's lemma, SGA 1 XIII 5.3 (Stacks 0EYG). Missing: tame covers along a
divisor (medium). -/
def L07_Abhyankar : Prop := sorry

/-- **L8** (P2). Grothendieck's semistable reduction theorem, SGA 7 IX 3.6. Missing: Néron
models (large). -/
def L08_SemistableReduction : Prop := sorry

/-- **L9** (P2). Raynaud's criterion, SGA 7 IX 4.7 / Silverberg–Zarhin Thm 3.5, Galois form:
`A[n] ⊂ A(F)`, `n ≥ 3`, `p ∤ n` ⇒ inertia unipotent on `V_ℓ(A)`, `ℓ ≠ p`. Missing: abelian
varieties with Tate modules (medium). -/
def L09_Raynaud : Prop := sorry

/-- **L10** (P2). Néron–Ogg–Shafarevich, Serre–Tate 1968 Thms 1-2. Missing: Tate modules,
good reduction (medium). -/
def L10_NeronOggShafarevich : Prop := sorry

/-- **L11a** (P3). Mumford §19 Thm 3: `rank Hom(A, B) ≤ 4 dim A dim B`. Missing: Hom groups of
abelian varieties (cheap-medium). -/
def L11a_RankHom : Prop := sorry

/-- **L11b** (P3). Mumford §19 Thm 4: characteristic polynomials on `V_ℓ` are integral and
independent of `ℓ`. Missing: Tate modules (medium). -/
def L11b_CharPolyIndep : Prop := sorry

/-- **L11c** (P3). Poincaré reducibility, Mumford §19 Thm 1. Missing: abelian subvarieties,
isogenies (medium). -/
def L11c_Poincare : Prop := sorry

/-- **L11d** (P3). Galois-equivariant Weil pairing; `GSp` with cyclotomic multiplier (Mumford
§§20, 23). Missing: polarizations, Tate modules (medium). -/
def L11d_WeilPairing : Prop := sorry

/-- **L11e** (P3). `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨` (Mumford §§19-20; Milne 1986 Thm 15.1(a)).
Missing: ℓ-adic étale cohomology (large). -/
def L11e_TateDuality : Prop := sorry

/-- **L11f** (P3). Extension of homomorphisms to good-reduction models (BLR §1.2 Prop. 8).
Missing: abelian schemes over a DVR (medium). -/
def L11f_NeronProperty : Prop := sorry

/-- **L12** (P3). Riemann, GAGA, rigidity: `End⁰(A_ℂ)` = Hodge endomorphisms;
`Hom_ℚ̄ = Hom_ℂ`. Missing: analytification (large). -/
def L12_RiemannGAGA : Prop := sorry

/-- **L13** (P3). Artin comparison, SGA 4 XI 4.4, with complex conjugation. Missing: as L12
(large). -/
def L13_ArtinComparison : Prop := sorry

/-- **L15(b)** (P4). `H²(G_ℚ, ±1) ≅ Br(ℚ)[2]`, compatible with localization. Missing: crossed
products, local invariants (medium). -/
def L15b_BrauerCohomology : Prop := sorry

/-- **L16** (P4). Local class field theory for finite extensions of `ℚ_p`, with norms and upper
numbering. Missing: local Artin map (medium; Tau Ceti). -/
def L16_LocalCFT : Prop := sorry

/-- **L20** (P4). Ramification groups: Hilbert's different formula, Herbrand, the subgroup
formula, the different bound, Artin and Swan conductors (Serre, *Corps locaux*). Missing: upper
numbering (medium; Tau Ceti). -/
def L20_RamificationGroups : Prop := sorry

/-- **L21** (P5). Faltings 1983 Satz 3, Satz 4, Kor. 1: semisimplicity of `V_ℓ(A)` and
`Hom_F(A,B) ⊗ ℚ_ℓ ≅ Hom_{G_F}(V_ℓA, V_ℓB)`. Missing: Tate modules (medium). -/
def L21_Faltings : Prop := sorry

/-- **L22** (P6). de Rham comparison (Scholze 2013 Cor. 1.8, Thms 9.1, 9.3, corrigendum 2016;
or Faltings 1989 / Tsuji 1999): `V_ℓ(A)` de Rham with weights `0, −1`, each of multiplicity `g`.
Missing: `B_dR` with Galois action and filtration, de Rham representations (large). -/
def L22_DeRhamComparison : Prop := sorry

/-- **L23** (P6). Fontaine, Astérisque 223 Thm 3.8: closure of de Rham representations under
duals, tensors, subquotients. Missing: as L22 (large). -/
def L23_FontaineClosure : Prop := sorry

/-- **L24** (P6). Berger 2002 Thm 0.7: de Rham ⇒ potentially semistable. Missing: `B_st`
(very large). -/
def L24_Berger : Prop := sorry

/-- **L25** (P6). Pan 2022 Thm 1.0.4: for odd `p`, a continuous irreducible
`ρ : G_ℚ → GL₂(ℚ̄_p)`, finitely ramified, potentially semistable at `p`, odd, with distinct
Hodge–Tate weights (and the `p = 3` residual clause) comes from a cuspidal eigenform up to
twist, read as: `∃ g` normalized eigenform, `∃ ψ` continuous character, with
`tr ρ(Frob_v) = ψ(Frob_v)·ι(a_v(g))` for almost all `v`. Expressible now except "potentially
semistable" (very large) and "Hodge–Tate weights" (large). -/
def L25_Pan : Prop := sorry

/-- **L26** (P6). Saito 1997 / Kato 2004 §9.4 / Scholl 1990: a semisimple `ρ` attached to a
weight-`k ≥ 2` eigenform of any level is Hodge–Tate at `ℓ` with weights `{0, 1−k}` (Tate
normalization). Missing: Hodge–Tate representations (large). -/
def L26_EigenformHT : Prop := sorry

/-- **L28(b)** (P7). Atkin–Lehner–Li (Li 1975 Thm 5): each eigensystem away from the level is
that of a unique newform; conjugates of newforms are newforms. Missing: old space and newforms
(medium; Tau Ceti). -/
def L28b_Newforms : Prop := sorry

/-- **L29** (P7). Eichler–Shimura (Shimura 1971 Thm 7.9, §7; Shimura 1973 Thm 1): for a weight-2
newform `f` of level `N`, `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a 2-dimensional `G_ℚ`-subquotient attached to
`f`. Missing: `X₁(N)` and `J₁(N)` over `ℚ` (very large). -/
def L29_EichlerShimura : Prop := sorry

/-- **L30** (P7). Carayol 1986 Thm (A): the Artin conductor exponent at `p ≠ ℓ` of the
representation attached to a weight-2 newform of level `N` is `v_p(N)`. Missing: conductors of
`ℓ`-adic representations (medium), newforms (medium). -/
def L30_Carayol : Prop := sorry

/-- **L31** (P8). Javanpeykar 2014 Thm 1.1.1: `h_F(Jac X) ≤ 13·10⁶ g deg_B⁵`. Missing: Faltings
height (very large). -/
def L31_Javanpeykar : Prop := sorry

/-- **L32** (P8). Gaudron–Rémond, Duke 163 (2014), Thm 1.4: isogeny of degree
`≤ ((14g)^{64g²}[K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`. Missing: Faltings height. -/
def L32_GaudronRemond : Prop := sorry

/-- **L33** (P8). Faltings 1983 Lemma 5: `|h_F(A) − h_F(B)| ≤ ½ log deg φ`; additivity; stability.
Missing: Faltings height. -/
def L33_FaltingsHeightLemma : Prop := sorry

/-- **L34** (P8). Bost (via GR14 §9): `h_F(A) ≥ −(3/2) dim A`. Missing: Faltings height. -/
def L34_Bost : Prop := sorry

/-- **L35** (P8). Pazuki 2012 Cor. 1.3(2), `g = 2`, `r = 2`:
`h_Θ(A) ≤ ½X_D + C₂ log(X_D + 2)`. Missing: Faltings height, theta constants. -/
def L35_Pazuki : Prop := sorry

/-! ## §3. Glue -/

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization). If the weights `{n, n+1−k}` of
`ρ_g ⊗ χ^n`-type twist equal `{0, −1}` with `k ≥ 1`, then `n = 0` and `k = 2`. -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **G16, numerics**: `∏_{p ≤ R, p prime} p^{E} ≤ R^{R·E}` (used with `E = E₀`). -/
theorem prod_primes_pow_le (R E : ℕ) :
    ∏ p ∈ (Finset.range (R + 1)).filter Nat.Prime, p ^ E ≤ R ^ (R * E) := by
  calc ∏ p ∈ (Finset.range (R + 1)).filter Nat.Prime, p ^ E
      ≤ ∏ _p ∈ (Finset.range (R + 1)).filter Nat.Prime, R ^ E := by
        refine Finset.prod_le_prod fun p hp => ?_
        have : p ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
        exact Nat.pow_le_pow_left this E
    _ = (R ^ E) ^ ((Finset.range (R + 1)).filter Nat.Prime).card := Finset.prod_const _
    _ ≤ (R ^ E) ^ R := by
        rcases Nat.eq_zero_or_pos R with rfl | hR
        · simp [Finset.filter_singleton, Nat.not_prime_zero]
        · refine Nat.pow_le_pow_right (pow_pos hR E) ?_
          calc ((Finset.range (R + 1)).filter Nat.Prime).card
              ≤ ((Finset.range (R + 1)).filter (fun p => 1 ≤ p)).card := by
                refine Finset.card_le_card fun p hp => ?_
                rw [Finset.mem_filter] at hp ⊢
                exact ⟨hp.1, hp.2.one_lt.le⟩
            _ = R := by
                rw [show (Finset.range (R + 1)).filter (fun p => 1 ≤ p) = Finset.Icc 1 R by
                  ext p; simp [Finset.mem_Icc, and_comm]]
                simp
    _ = R ^ (R * E) := by rw [← pow_mul, mul_comm]

/-- **G0 without G20.** The leaves imply the `j`-form of H, `JHeightBound Mult.S_mul`
(steps A1-F3; glue G1-G19). Not proved: most leaves are placeholders. -/
theorem jHeightBound_of_leaves
    (_l1 : L01_ShimuraDeligne) (_l2 : L02_BabaGranath) (_l3 : L03_LinYang) (_l4 : L04_Igusa)
    (_l5 : L05_GonzalezRotger) (_l6 : L06_Purity) (_l7 : L07_Abhyankar)
    (_l8 : L08_SemistableReduction) (_l9 : L09_Raynaud) (_l10 : L10_NeronOggShafarevich)
    (_l11a : L11a_RankHom) (_l11b : L11b_CharPolyIndep) (_l11c : L11c_Poincare)
    (_l11d : L11d_WeilPairing) (_l11e : L11e_TateDuality) (_l11f : L11f_NeronProperty)
    (_l12 : L12_RiemannGAGA) (_l13 : L13_ArtinComparison) (_l14 : SkolemNoether)
    (_l15a : HasseBrauerQ) (_l15b : L15b_BrauerCohomology) (_l16 : L16_LocalCFT)
    (_l17 : KroneckerWeber) (_l18 : FrobeniusDense) (_l19 : BrauerNesbitt)
    (_l20 : L20_RamificationGroups) (_l21 : L21_Faltings) (_l22 : L22_DeRhamComparison)
    (_l23 : L23_FontaineClosure) (_l24 : L24_Berger) (_l25 : L25_Pan) (_l26 : L26_EigenformHT)
    (_l27a : EigenformRepExists) (_l27b : DeligneSerreConseq) (_l28a : EigenformTwist)
    (_l28b : L28b_Newforms) (_l29 : L29_EichlerShimura) (_l30 : L30_Carayol)
    (_l31 : L31_Javanpeykar) (_l32 : L32_GaudronRemond) (_l33 : L33_FaltingsHeightLemma)
    (_l34 : L34_Bost) (_l35 : L35_Pazuki) :
    ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul := by
  sorry

/-- **G0. The leaves imply `SixContactMin`**, through G20 (`sixContactMin_of_jHeightBound`,
proved in `ZInQKernel/Hypotheses/JHeight.lean`). -/
theorem sixContactMin_of_leaves
    (l1 : L01_ShimuraDeligne) (l2 : L02_BabaGranath) (l3 : L03_LinYang) (l4 : L04_Igusa)
    (l5 : L05_GonzalezRotger) (l6 : L06_Purity) (l7 : L07_Abhyankar)
    (l8 : L08_SemistableReduction) (l9 : L09_Raynaud) (l10 : L10_NeronOggShafarevich)
    (l11a : L11a_RankHom) (l11b : L11b_CharPolyIndep) (l11c : L11c_Poincare)
    (l11d : L11d_WeilPairing) (l11e : L11e_TateDuality) (l11f : L11f_NeronProperty)
    (l12 : L12_RiemannGAGA) (l13 : L13_ArtinComparison) (l14 : SkolemNoether)
    (l15a : HasseBrauerQ) (l15b : L15b_BrauerCohomology) (l16 : L16_LocalCFT)
    (l17 : KroneckerWeber) (l18 : FrobeniusDense) (l19 : BrauerNesbitt)
    (l20 : L20_RamificationGroups) (l21 : L21_Faltings) (l22 : L22_DeRhamComparison)
    (l23 : L23_FontaineClosure) (l24 : L24_Berger) (l25 : L25_Pan) (l26 : L26_EigenformHT)
    (l27a : EigenformRepExists) (l27b : DeligneSerreConseq) (l28a : EigenformTwist)
    (l28b : L28b_Newforms) (l29 : L29_EichlerShimura) (l30 : L30_Carayol)
    (l31 : L31_Javanpeykar) (l32 : L32_GaudronRemond) (l33 : L33_FaltingsHeightLemma)
    (l34 : L34_Bost) (l35 : L35_Pazuki) :
    ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound
    (jHeightBound_of_leaves l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11a l11b l11c l11d l11e l11f l12 l13
      l14 l15a l15b l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27a l27b l28a l28b l29 l30 l31
      l32 l33 l34 l35)

end HDec

end

#print axioms HDec.weight_match
#print axioms HDec.prod_primes_pow_le
#print axioms HDec.EigenformTwist
