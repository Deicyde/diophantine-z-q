import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Basic

/-!
# Kato's theorems used in the proof of Theorem 5.3

Lane RC9. All Kato references are to K. Kato, *`p`-adic Hodge theory and values of zeta functions
of modular forms*, Astérisque 295 (2004), 117–290 (read for this lane from the Numdam scan; page
numbers are those of the volume).

Uses in the manuscript (`diophantine_zq.tex`):
* tex 1104–1108 (`lem:forward-rank`): the `r = 0` finiteness from **Cor. 14.3** "applied to the
  modular quotient `J₁(N) ↠ A` over `ℚ` and the trivial character"; with Kolyvagin's Theorem 1 it
  gives `corank Sel_{2^∞} = 0` for the companion twists (tex 2604–2647: `s₂(E^{(k)}/ℚ) = 0`), and
  finite `Ш` in the calibration (tex 4020–4021, 5250).
* tex 1884–1893 and App. E ¶7 (tex 7206–7255): the divisibility **Thm. 13.4(2)** at height-one
  primes not containing `2`, with its hypotheses (i)–(v) checked; (i) via **Thm. 13.5(2)**
  (Rohrlich, tex 7215–7221).
* App. E ¶4 (tex 7005–7023), ¶5 (tex 7074–7092): the norm relation **Prop. 8.12** (p. 186), which
  makes the twisted classes (K8) an Euler system in the sense of **13.1** (pp. 224–225, (13.1.1)).
* App. E ¶1–¶6 also cite (8.1.3) p. 180, 8.2 pp. 180–181, 8.9 p. 185, 8.11, 13.6–13.7 p. 227,
  (4.2.4) p. 143, Thm. 6.6 p. 163, Thm. 9.7 p. 189, (12.2.1)–(12.2.3) p. 220: the construction and
  the explicit reciprocity law. These enter here only through the interface `KatoZetaInterface`
  (field `recip`), not as separate leaves.

## What is genuine and what is an interface

* `KatoCor14_3` (PRINT) and `KatoThm13_5_2` (PRINT) are stated over genuine definitions: Mathlib's
  `L`-series and Dirichlet characters, the tree's `Ш(E/ℚ)` and `Sel_{2^∞}(E/ℚ)`.
* Kato's zeta elements, the étale cohomology groups `H¹(ℤ[ζ_m, 1/p], T)`, the Iwasawa modules
  `𝐇^q(T)` and the dual exponential do not exist in Mathlib. `EulerSystemData` (Kato 13.1) and
  `IwasawaData` (the data of Thm. 13.4) are abstract interfaces with exactly the properties the
  proof uses; `KatoZetaInterface` bundles them for a fixed curve, together with Prop. 8.12 /
  Example 13.3 (the Euler-system relation with `P_ℓ(t) = 1 - a_ℓ t + ℓ t²`), Thm. 13.4(1)(2), and
  the central-value anchor (Thm. 6.6 with Thm. 9.7). **Vacuity:** with abstract modules the
  relation alone is satisfied by the zero system (`EulerSystemData.zero_isEulerSystem`); the only
  genuine anchor is `recip`, which forces nonzero classes whenever a genuine partial `L`-value is
  nonzero (`KatoZetaInterface.z_ne_zero_of_L_ne_zero`). The Iwasawa modules stay unanchored; see
  the sizing note at `KatoZetaInterface`.
* `z2Corank_zero_of_finite`, `forward_rank_zero` (PROVED): the `r = 0` half of `lem:forward-rank`
  from `KatoCor14_3` and `BCDTThmA`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsArith

open scoped WeierstrassCurve
open ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53

/-! ### Corollary 14.3 (rank-zero finiteness) -/

/-- **Kato, Astérisque 295, Corollary 14.3, p. 235** (PRINT), in the case used: `K = ℚ`, `χ`
trivial, `A = E` an elliptic curve. The print: *let `A` be an abelian variety over `ℚ` with a
surjective homomorphism `J₁(N) → A` for some `N ≥ 1`; let `K` be a finite abelian extension of `ℚ`,
`χ : Gal(K/ℚ) → ℂ^×` a character, and assume `L(A, χ, 1) ≠ 0`. Then (1) the `χ`-part of
`Sel(K, A ⊗_ℚ K)` is finite; (2) the `χ`-part of `A(K)` is finite.* Here `Sel(ℚ, A) = ⊕_p
Sel(ℚ, T_p A)` is the usual Selmer group (p. 235).

Lean form (DEPARTURES, each with its reason):
* `J₁(N) ↠ E` (Jacobians are absent from Mathlib) is replaced by `PoleS12.IsModular E`; for an
  elliptic curve over `ℚ` the two are equivalent (Eichler–Shimura and Faltings' isogeny theorem;
  GLUE), and both hold for every `E/ℚ` by BCDT (`PoleS12.BCDTThmA`).
* `L(E, 1) ≠ 0` is the shared top layer's `AnalyticRank E 0` (`analyticRank_zero_iff`).
* The conclusion (1) ∧ (2) is stated as `E(ℚ)` finite ∧ `Ш(E/ℚ)` finite ∧ `Sel_{2^∞}(E/ℚ)` finite.
  The first two are equivalent to (1) ∧ (2) by the Kummer sequence
  `0 → E(ℚ) ⊗ ℚ/ℤ → Sel(ℚ, E) → Ш(E/ℚ) → 0` (GLUE); the third is the `2`-component of (1)
  (Bloch–Kato `Sel(ℚ, T₂E) = Sel_{2^∞}(E/ℚ)`, GLUE).

Use: tex 1104–1108 ("applied to the modular quotient `J₁(N) ↠ A` over `ℚ` and the trivial
character. This result includes the prime two and imposes no residual irreducibility hypothesis").
The use matches the hypotheses. -/
def KatoCor14_3 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → AnalyticRank E 0 →
    Finite E.toAffine.Point ∧ Finite (sha E) ∧ Finite (selmerTwoPower E)

/-- A finite module has `ℤ₂`-corank zero. -/
theorem z2Corank_zero_of_finite (M : Type) [AddCommGroup M] [Finite M] : Z2Corank M 0 := by
  refine ⟨M, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
    { toFun := fun m => (fun i => Fin.elim0 i, m)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by
        ext i
        · exact Fin.elim0 i
        · rfl
      map_add' := fun a b => by
        ext i
        · exact Fin.elim0 i
        · rfl }

/-- **The `r = 0` half of `lem:forward-rank` (tex 1086–1108)**, PROVED from Kato's Cor. 14.3 and
BCDT: an elliptic curve `E/ℚ` with `L(E, 1) ≠ 0` has finite `E(ℚ)`, finite `Ш(E/ℚ)`, and
`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 0`. Used for the companion twist at tex 2627–2647
(`s₂(E^{(k)}/ℚ) = 0`). -/
theorem forward_rank_zero (hK : KatoCor14_3) (hB : BCDTThmA) (E : WeierstrassCurve ℚ)
    (hE : E.IsElliptic) (hL : AnalyticRank E 0) :
    Finite E.toAffine.Point ∧ Finite (sha E) ∧ Z2Corank (selmerTwoPower E) 0 := by
  obtain ⟨h1, h2, h3⟩ := hK E hE (hB E hE) hL
  exact ⟨h1, h2, z2Corank_zero_of_finite _⟩

/-! ### Theorem 13.5(2) (Rohrlich) -/

/-- **Kato, Astérisque 295, Theorem 13.5(2), p. 227** (PRINT; Kato attributes it to Rohrlich
[Ro2]), in weight `k = 2` for the newform of `E`: *assume `k` is even; let `S` be a finite set of
prime numbers; then the set of `χ ∈ ⋃_{m ≥ 1, prime(m) ⊆ S} Hom((ℤ/m)^×, ℂ^×)` with
`L_S(f, χ, k/2) = 0` is finite* (characters identified along `m ∣ m'`).

Lean form: `L_S(E, χ, 1) = 0` is `LSValueVanishes E S χ` (the continuation of
`∑_{(n,S)=1} a_n(E) χ(n) n^{-s}` vanishes at `1`); the identification along `m ∣ m'` is realized
by `charOnPrimeToS S χ` (the values of `χ` on integers prime to `S`), which is injective on Kato's
union and on which `L_S(E, χ, s)` depends. DEPARTURE: the newform `f` is the cusp form of
`PoleS12.IsModular E`, whose coefficients are Mathlib's `a_n(E)`.

Use: App. E ¶7, tex 7215–7221 ("only finitely many zero `L`-values among characters supported on
the fixed finite set `prime(2Nd)`"), to verify hypothesis (i) of Thm. 13.4 for the twisted system,
following Kato's own Prop. 13.7. Here `S = prime(2Nd)` and `k = 2`: the use matches. -/
def KatoThm13_5_2 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      Set.Finite {g : ℕ → ℂ | ∃ (m : ℕ) (_ : m ≠ 0) (_ : m.primeFactors ⊆ S)
        (χ : DirichletCharacter ℂ m), g = charOnPrimeToS S χ ∧ LSValueVanishes E S χ}

/-! ### Euler systems (Kato 13.1) as an interface -/

/-- `Ξ = {m ≥ 1 : prime(m) ∩ Σ = {p}}` (Kato 13.1, p. 224). -/
def KatoXi (p : ℕ) (Sig : Finset ℕ) (m : ℕ) : Prop :=
  1 ≤ m ∧ p ∣ m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∈ Sig → q = p

/-- The arithmetic Frobenius `σ_ℓ ∈ Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×` of a prime `ℓ ∤ m` (`ζ ↦ ζ^ℓ`);
the identity when `ℓ` is not prime to `m` (never used there). -/
def frobUnit (m ℓ : ℕ) : (ZMod m)ˣ :=
  if h : Nat.Coprime ℓ m then ZMod.unitOfCoprime ℓ h else 1

open Classical in
/-- `ℓ⁻¹ ∈ O` when `ℓ` is a unit of `O` (junk value `0` otherwise, never used). -/
def invNat (O : Type*) [CommRing O] (ℓ : ℕ) : O :=
  if h : IsUnit (ℓ : O) then ↑h.unit⁻¹ else 0

/-- `P(ℓ^{-1} σ^{-1}) ∈ O[G]` for `P = ∑ c_i t^i ∈ O[t]`: `∑ c_i ℓ^{-i} [σ^{-i}]`. -/
def eulerFactor {O G : Type*} [CommRing O] [CommGroup G] (P : Polynomial O) (ℓinv : O) (σ : G) :
    MonoidAlgebra O G :=
  ∑ i ∈ P.support, MonoidAlgebra.single (σ⁻¹ ^ i) (P.coeff i * ℓinv ^ i)

/-- **The data of an Euler system (Kato 13.1, pp. 224–225), as an interface.** For each
`m ∈ Ξ` an `O[(ℤ/m)^×]`-module `H m` (standing for `H¹(ℤ[ζ_m, 1/p], T)`, Kato 8.2), the norm maps
`H m' → H m` for `m ∣ m'`, and classes `z m ∈ H m`. ABSTRACT: the cohomology groups are not
defined here (see `KatoZetaInterface` for the sizing). -/
structure EulerSystemData (O : Type) [CommRing O] where
  /-- `H¹(ℤ[ζ_m, 1/p], T)`. -/
  H : ℕ → Type
  [addCommGroup : ∀ m, AddCommGroup (H m)]
  [module : ∀ m, Module (MonoidAlgebra O (ZMod m)ˣ) (H m)]
  /-- The norm (corestriction) map `H¹(ℤ[ζ_{m'}, 1/p], T) → H¹(ℤ[ζ_m, 1/p], T)` for `m ∣ m'`. -/
  cor : ∀ m m' : ℕ, m ∣ m' → H m' →+ H m
  /-- The classes `z_m`. -/
  z : ∀ m, H m

attribute [instance] EulerSystemData.addCommGroup EulerSystemData.module

/-- **Kato's Euler-system relation (13.1.1), p. 225**: for `m, m' ∈ Ξ` with `m ∣ m'`, the norm
map sends `z_{m'}` to `(∏_ℓ P_ℓ(ℓ^{-1}σ_ℓ^{-1})) · z_m`, `ℓ` over the primes dividing `m'` but not
`m`, `σ_ℓ` the arithmetic Frobenius of `ℓ` in `Gal(ℚ(ζ_m)/ℚ)`, and `P_ℓ(t) = det(1 - Fr_ℓ t | T)`. -/
def EulerSystemData.IsEulerSystem {O : Type} [CommRing O] (D : EulerSystemData O) (p : ℕ)
    (Sig : Finset ℕ) (P : ℕ → Polynomial O) : Prop :=
  ∀ m m' : ℕ, KatoXi p Sig m → KatoXi p Sig m' → ∀ h : m ∣ m',
    D.cor m m' h (D.z m') =
      (∏ ℓ ∈ m'.primeFactors \ m.primeFactors, eulerFactor (P ℓ) (invNat O ℓ) (frobUnit m ℓ)) •
        D.z m

/-- **Vacuity of the bare relation**: the zero system is an Euler system for every `P`. So the
relation alone carries no information; `KatoZetaInterface.recip` is the anchor. -/
theorem EulerSystemData.zero_isEulerSystem {O : Type} [CommRing O] (H : ℕ → Type)
    [∀ m, AddCommGroup (H m)] [∀ m, Module (MonoidAlgebra O (ZMod m)ˣ) (H m)]
    (p : ℕ) (Sig : Finset ℕ) (P : ℕ → Polynomial O) :
    (EulerSystemData.mk H (fun _ _ _ => 0) (fun _ => 0)).IsEulerSystem p Sig P := by
  intro m m' _ _ h
  simp

/-! ### Theorem 13.4 (the Euler-system divisibility) as an interface -/

/-- **The data of Kato's Theorem 13.4 (p. 226), as an interface.** A commutative ring `Λ`
(standing for `O_L[[G_∞]]`, `G_∞ = Gal(ℚ(ζ_{p^∞})/ℚ)`, Kato 12.1), modules `H1 = 𝐇¹(T)`,
`H2 = 𝐇²(T)`, `H2loc = 𝐇²_loc(T)` (Kato 12.2), the localization map, and the images
`zIw n = z_{p^n}` of the Euler system in `𝐇¹(T)`. ABSTRACT. -/
structure IwasawaData (Λ : Type) [CommRing Λ] where
  /-- `𝐇¹(T) = lim_n H¹(ℤ[ζ_{p^n}, 1/p], T)`. -/
  H1 : Type
  /-- `𝐇²(T)`. -/
  H2 : Type
  /-- `𝐇²_loc(T) = lim_n H²(ℚ_p(ζ_{p^n}), T)`. -/
  H2loc : Type
  [acg1 : AddCommGroup H1]
  [mod1 : Module Λ H1]
  [acg2 : AddCommGroup H2]
  [mod2 : Module Λ H2]
  [acg3 : AddCommGroup H2loc]
  [mod3 : Module Λ H2loc]
  /-- The localization `𝐇²(T) → 𝐇²_loc(T)`. -/
  loc : H2 →ₗ[Λ] H2loc
  /-- The image `(z_{p^n})_n` of the Euler system in `𝐇¹(T)`. -/
  zIw : H1

attribute [instance] IwasawaData.acg1 IwasawaData.mod1 IwasawaData.acg2 IwasawaData.mod2
  IwasawaData.acg3 IwasawaData.mod3

/-- `Z`: the `Λ`-submodule of `𝐇¹(T)` generated by `(z_{p^n})_n` (Thm. 13.4). -/
def IwasawaData.Z {Λ : Type} [CommRing Λ] (D : IwasawaData Λ) : Submodule Λ D.H1 :=
  Submodule.span Λ {D.zIw}

/-- `J`: the ideal of `Λ` generated by `h(Z)` for all `Λ`-homomorphisms `h : 𝐇¹(T) → Λ`. -/
def IwasawaData.J {Λ : Type} [CommRing Λ] (D : IwasawaData Λ) : Ideal Λ :=
  ⨆ h : D.H1 →ₗ[Λ] Λ, D.Z.map h

/-- `𝐇²(T)₀ = Ker(𝐇²(T) → 𝐇²_loc(T))`. -/
def IwasawaData.H2zero {Λ : Type} [CommRing Λ] (D : IwasawaData Λ) : Submodule Λ D.H2 :=
  LinearMap.ker D.loc

/-- **The conclusion of Kato's Theorem 13.4 (1) and (2), p. 226**: (1) `𝐇²(T)` is a torsion
`Λ`-module; (2) for every prime `𝔭` of `Λ` of height one not containing `p`,
`length_{Λ_𝔭}(𝐇²(T)_{0,𝔭}) ≤ length_{Λ_𝔭}(Λ_𝔭/J_𝔭)`. -/
def IwasawaData.Thm13_4Conclusion {Λ : Type} [CommRing Λ] (D : IwasawaData Λ) (p : Λ) : Prop :=
  Module.IsTorsion Λ D.H2 ∧
    ∀ (𝔭 : Ideal Λ) [𝔭.IsPrime], 𝔭.height = 1 → p ∉ 𝔭 →
      Module.length (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl D.H2zero) ≤
        Module.length (Localization.AtPrime 𝔭)
          (Localization.AtPrime 𝔭 ⧸ D.J.map (algebraMap Λ (Localization.AtPrime 𝔭)))

/-! ### Kato's zeta elements for `E`: the interface the proof uses -/

/-- `Λ = ℤ₂[[G_∞]] ≅ ℤ₂[Δ][[T]]`, `Δ = Gal(ℚ(i)/ℚ) ≅ ℤ/2`, `T = [γ] - 1` for a topological
generator `γ` of `G¹_∞ ≅ 1 + 4ℤ₂` (Kato 12.1, p. 219, case `p = 2`). -/
abbrev KatoLambda2 : Type := PowerSeries (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2)))

/-- `P_ℓ(t) = det(1 - Fr_ℓ t | T₂E) = 1 - a_ℓ t + ℓ t²` (Kato, Example 13.3, p. 225, in weight
`k = 2`, `r = 1`, trivial nebentypus, rational `a_ℓ`). -/
def katoP (E : WeierstrassCurve ℚ) (ℓ : ℕ) : Polynomial ℤ_[2] :=
  1 - Polynomial.C ((E.LFunction ℓ : ℤ) : ℤ_[2]) * Polynomial.X + Polynomial.C (ℓ : ℤ_[2]) *
    Polynomial.X ^ 2

/-- **Kato's zeta elements for `E` at `p = 2`: the interface the proof uses** (App. E). For the
fixed curve `E` and a finite set `Σ ∋ 2` containing the primes of bad reduction:

* `es` with `es_euler`: Kato's elements form an Euler system for `(T₂E, ℚ₂, Σ)`
  (**Prop. 8.12, p. 186**, via **Example 13.3, p. 225**);
* `iw` with `iw_z` and `iw_thm13_4`: the Iwasawa data of the same system, and the conclusion of
  **Thm. 13.4(1)(2), p. 226** at height-one primes not containing `2` (its hypotheses (i)–(v) are
  verified in the manuscript at tex 7206–7232: (i) by Thm. 13.5(2), (v) by Serre's open image);
* `recip`, the **central-value anchor** (Thm. 6.6, p. 163, with Thm. 9.7, p. 189; manuscript
  (K12)–(K13), tex 7118–7142): a linear functional `per m` on `H m` (the period of the dual
  exponential) such that for every Dirichlet character `χ` modulo `m ∈ Ξ` the `χ`-weighted sum of
  the Galois translates of `z_m` has period `s · b(χ) · L_{prime(mN)}(E, χ, 1)`, with the fixed
  smoothing scalar `s ≠ 0` and nonzero period constants `b(χ)`. Here `L_S(E, χ, 1)` is the value at
  `1` of a fixed entire continuation `Lcont` of the genuine partial twisted `L`-series.

**Sizing a genuine definition.** Replacing the abstract fields needs, beyond the vendored Galois
cohomology: (a) `H¹(ℤ[ζ_m, 1/p], T)` as continuous cohomology of `Gal(ℚ̄/ℚ(ζ_m))` with
`T/p^n`-coefficients, cut out by vanishing of restriction to inertia at the primes not above `p`,
and its inverse limit (decomposition and inertia groups of `ℚ̄` at all places; a few thousand
lines); (b) corestriction and the group-ring structure (several hundred lines); (c) `𝐇^q(T)` over
`ℤ₂[[G_∞]]` and the identification of the completed group ring (about a thousand lines);
(d) Kato's elements themselves, built from Beilinson's elements in `K₂` of modular curves and the
étale regulator (absent; tens of thousands of lines); (e) Fontaine's `D_dR`, `B_dR` and the dual
exponential for `recip` (absent; a major project). -/
structure KatoZetaInterface (E : WeierstrassCurve ℚ) (Sig : Finset ℕ) where
  /-- Kato's Euler system `(z_m)_{m ∈ Ξ}` in `H¹(ℤ[ζ_m, 1/2], T₂E)`. -/
  es : EulerSystemData ℤ_[2]
  /-- **Prop. 8.12 / Example 13.3**: the Euler-system relation with `P_ℓ = 1 - a_ℓ t + ℓ t²`. -/
  es_euler : es.IsEulerSystem 2 Sig (katoP E)
  /-- The Iwasawa data `𝐇¹, 𝐇², 𝐇²_loc` over `Λ = ℤ₂[[G_∞]]`, with `zIw = (z_{2^n})_n`. -/
  iw : IwasawaData KatoLambda2
  /-- **Thm. 13.4(1)(2)** for this system. -/
  iw_thm13_4 : iw.Thm13_4Conclusion 2
  /-- The period of the dual exponential on `H m`. -/
  per : ∀ m, es.H m →+ ℂ
  /-- The fixed smoothing scalar of the retained-smoothed elements. -/
  s : ℂ
  s_ne_zero : s ≠ 0
  /-- The fixed nonzero rational period constants `b_ε` (one per sign `χ(-1)`). -/
  b : ∀ {m : ℕ}, DirichletCharacter ℂ m → ℂ
  b_ne_zero : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m), b χ ≠ 0
  /-- An entire continuation of each genuine partial twisted `L`-series `L_{prime(mN)}(E, χ, s)`
  (`N` enters through `Sig`, which contains the bad primes). -/
  Lcont : ∀ {m : ℕ}, DirichletCharacter ℂ m → ℂ → ℂ
  Lcont_entire : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m), Differentiable ℂ (Lcont χ)
  Lcont_eq : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m) (s : ℂ), 3 / 2 < s.re →
    Lcont χ s = LSeries (twistedCoeffS E (Sig ∪ m.primeFactors) χ) s
  /-- **The central-value anchor** (Thm. 6.6 with Thm. 9.7): the `χ`-weighted sum of the Galois
  translates of `z_m` has period `s · b(χ) · L_{prime(mN)}(E, χ, 1)`. -/
  recip : ∀ (m : ℕ) [NeZero m], KatoXi 2 Sig m → ∀ χ : DirichletCharacter ℂ m,
    ∑ g : (ZMod m)ˣ, χ (g : ZMod m) * per m (MonoidAlgebra.of ℤ_[2] (ZMod m)ˣ g • es.z m) =
      s * b χ * Lcont χ 1

/-- **Non-vacuity of the anchor**: in any `KatoZetaInterface`, `z_m ≠ 0` as soon as one genuine
partial `L`-value `L_{prime(mN)}(E, χ, 1)` with `χ` modulo `m ∈ Ξ` is nonzero. So the interface
cannot be filled by the zero system unless all these genuine values vanish. -/
theorem KatoZetaInterface.z_ne_zero_of_L_ne_zero {E : WeierstrassCurve ℚ} {Sig : Finset ℕ}
    (K : KatoZetaInterface E Sig) {m : ℕ} [NeZero m] (hm : KatoXi 2 Sig m)
    (χ : DirichletCharacter ℂ m)
    (hL : K.Lcont χ 1 ≠ 0) : K.es.z m ≠ 0 := by
  intro hz
  have h := K.recip m hm χ
  simp only [hz, smul_zero, map_zero, mul_zero, Finset.sum_const_zero] at h
  exact mul_ne_zero (mul_ne_zero K.s_ne_zero (K.b_ne_zero χ)) hL h.symm

/-- **Kato's construction for `E` (PRINT over the interface `KatoZetaInterface`)**: for an
elliptic curve `E/ℚ` without complex multiplication and a finite set `Σ` of primes containing `2`
and the primes of bad reduction, Kato's zeta elements furnish a `KatoZetaInterface E Σ`
(Prop. 8.12, Example 13.3, Thm. 13.4(1)(2), Thms. 6.6 and 9.7 of Kato, Astérisque 295). The
non-CM hypothesis is the one under which §13 proves Thm. 13.4's hypothesis (v) (p. 226: "if `f`
has CM, this theorem is not applied because the condition (v) is not satisfied"). The condition on
`Σ` says that outside `Σ` the given model is integral with unit discriminant, so `Σ` contains `2`
and every prime of bad reduction (Kato 13.1: `Σ` contains `p` and the primes where `T` ramifies).
-/
def KatoZetaLeaf : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], HasNoCM E → ∀ Sig : Finset ℕ, 2 ∈ Sig →
    (∀ p : ℕ, p.Prime → p ∉ Sig →
      (¬ p ∣ E.a₁.den ∧ ¬ p ∣ E.a₂.den ∧ ¬ p ∣ E.a₃.den ∧ ¬ p ∣ E.a₄.den ∧ ¬ p ∣ E.a₆.den) ∧
        ¬ (p : ℤ) ∣ E.Δ.num) →
    Nonempty (KatoZetaInterface E Sig)

end ZInQ.Manuscript.RC.PrintsArith
