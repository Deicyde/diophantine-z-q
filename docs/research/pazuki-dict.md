# pazuki-dict: `pazukiCor13Upper` reduced to Pazuki's corollary for algebraic `(A, L)`

Task pazuki-dict, 2026-11-16. Base origin/main 2880fef1 (leaf-fold31).
Lean: `ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean` (namespace `PazukiDict`). Log: `scratch/pazuki-dict/log.md`.
Autofold spec: `scratch/pazuki-dict/autofold.json`.
Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, reference given), **SPECULATIVE**;
theorem numbers recalled without a source are **UNVERIFIED** (no network). Model work, no human review.

## 0. Verdict and main result

**Option (b), with the hypothesis direction fixed.** `pazukiCor13Upper` is not in printed form as stated. It is
a consequence of Pazuki's corollary that needs two further steps:

1. **The weak-uniformization step.** It quantifies over leaf-push2's weak `IsUniformization`: a surjective analytic
   homomorphism `ℂ² → A(ℂ)_σ` with kernel `Λ`. Under the lead's 11-16 ruling, going from these clauses to the
   biholomorphic uniformization is a step. The field accepts the weak predicate as the print's uniformization. Fixed:
   the new leaf takes bp-analytic's strong (biholomorphic) uniformization, and the step is **proved in Lean**
   (`exists_strong_of_weak`).
2. **The analytic-to-algebraic step.** The field quantifies over every *analytic* principal polarization of `ℂ²/Λ`
   (`IsSiegel Ω ∧ IsPeriodMatrix Λ Ω`), while Pazuki's print is about algebraic `(A, L)`. The consumer chain needs
   this direction: its `Ω` is the QM period matrix `Ω(τ)` from `FibreQMPeriodAll`, an analytic polarization. This
   step is isolated as one named Prop, `AnalyticPPAlgebraic`, rated **GLUE (composite)**.

The analytic-to-algebraic direction is not a single printed theorem. It needs Appell–Humbert/Frobenius, GAGA/Chow,
and `NS(A_ℚ̄) = NS(A_ℂ)`, and none of these can be stated in Lean today over genuine analytic definitions (Mathlib has
no analytic line bundles). So the target "pazukiCor13Upper back to LEAF" is met **only for the new leaf**: the field
is replaced by one printed-form LEAF and one composite GLUE, plus the existing field `uniformizationLeafAll`.

Main theorem (VERIFIED, compiled; axioms `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem PazukiDict.pazukiCor13Upper_of_printed (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hA : AnalyticPPAlgebraic) (hP : PazukiCor13UpperPP) : ZInQ.HeightSplit.PazukiCor13Upper
```

- `hU` is the existing textbook field `uniformizationLeafAll`. unif-printed proves it from four printed leaves.
- `PazukiCor13UpperPP` is the new leaf: Pazuki Cor. 1.3(2), upper half, for algebraic `(A_{K'}, L)`. It is rated
  **printed form**. It keeps the reading risk that was already open (Def. 2.6 coordinates).
- `AnalyticPPAlgebraic` is new GLUE (composite). It also splits, by a proved theorem, into an analytic half over `ℂ`
  and an arithmetic half (§2.3).

No statement was changed. `PazukiCor13Upper` is not false or vacuous as stated: it follows from the three
hypotheses above, and they are true (modulo the old Def. 2.6 reading risk).

## 1. The field and its gaps (VERIFIED, read)

- `kinds.tsv`, row `pazukiCor13Upper`: research, published, LEAF/LEAF. Source: Pazuki, Bull. SMF 140 (2012),
  Cor. 1.3(2), upper half.
- The statement is `ZInQKernel/OneProof/H/TailY.lean:778` (`ZInQ.HeightSplit.PazukiCor13Upper`). For an abelian
  surface `A/K` with stable height `x`, every `σ`, every weak uniformization `(Λ, Φ)`, every `Ω ∈ 𝔥₂` with
  `IsPeriodMatrix Λ Ω`, and every algebraic representative `z` of `[θ_m(0, Ω)]`:
  `max 1 h₂(z) − max 1 (x + log π)/2 ≤ C₂ log(min(…) + 2)`.
- Its own docstring lists the gaps: the Def. 2.6 identification (UNVERIFIED), and "the algebraicity over `ℚ̄` of
  every analytic principal polarization (Riemann/Lefschetz; standard)".
- **Lead's 11-16 ruling: yes, the field accepts the weak `IsUniformization`** (`ZInQ.LeafPush2.IsUniformization`,
  `ZInQKernel/HDecomp/LeafPush2/R22.lean`). That predicate has no local-coordinate clause and no continuity of the
  inverse. So reading it as "the uniformization `A(ℂ) = ℂ²/Λ`" of the print is a step: one must show that a bijective
  holomorphic homomorphism is biholomorphic and that `Λ` is the period lattice.
- **Where the consumer's `Ω` comes from (VERIFIED, read).** `r22_of_upper` (TailY) feeds `R22_Pazuki`. That goes to
  `thetaPazuki` (LPrefix) through `ThetaPointOfFibre`, then `thetaPointOfFibre_of` and `fibreThetaF1_of_qm`
  (TailA, `ThetaPt`). There `Ω = Ω(τ)` is the period matrix of the analytic QM polarization `Trd(μ⁻¹xȳ)` of
  `ℂ²/Λ_τ`. So the direction the consumers need is **analytic ⇒ algebraic**: a printed leaf over algebraic `(A, L)`
  can only be applied to that `Ω` after showing it is the period matrix of some algebraic `L`.

## 2. The new statements (verbatim from the Lean file)

### 2.1 Genuine definitions

- **`riemannTheta Ω z`.** Riemann's theta function `∑_{n ∈ ℤ²} exp(πi nᵀΩn + 2πi nᵀz)`, as a `tsum` (the same
  pattern as the kernel's `thetaConst`).
- **`liftPt A σ σ' hσ p`.** For `σ = σ' ∘ (K → K')`, the complex point `(p, Spec σ') : Spec ℂ → A ×_K K'` of the
  base change `(A.baseChange K').X.left`, built with `pullback.lift`.
- **`OnZeroLocus s q`.** `q` lies in the support of the zero scheme of `s : 𝒪 → ℳ`. The zero scheme is the vendored
  `Scheme.Modules.Hom.zeroLocus` (Jacobian-Challenge).
- **`IsSymmPrincipal B L`.** Three conditions on `L ∈ Pic(B)`:
  - ample: t09-pic's `T09Pic.IsAmple`, Stacks 01PS;
  - symmetric: `Scheme.Pic.map (GrpObj.inv).left L = L`;
  - `Module.finrank Γ(B, 𝒪) Γ(ℒ, ⊤) = 1`.

  The `Module` instance was checked by `#synth`: it is the natural one, `Scheme.Modules.instModule…`.
- **`IsThetaPeriodMatrix A σ σ' hσ L Λ φ Ω`.** There are three objects:
  - a `ℂ`-linear `T : ℂ^g ≃ ℂ²` with `T(Λ) = Ωℤ² + ℤ²`;
  - a vector `c ∈ ℂ²`;
  - a section `s` of `L`.

  They satisfy, for all `w`: `liftPt(ptE(φ(w))) ∈ Z(s) ⟺ θ(Tw + c, Ω) = 0`. Here `ptE : A_ℂ(ℂ) ≃ A(ℂ)_σ` is
  av-split's map.

  This is "`Ω` is the period matrix of `(A_σ, L)` in the symplectic basis `T`". For `L` ample, symmetric, with
  `h⁰ = 1`, the divisor of `s` is reduced (`D² = 2`, so `D = C` irreducible or `D = E₁ + E₂`). Then equality of the
  supports gives equality of the divisors, hence of the Riemann forms (Riemann's theorem on the theta divisor;
  Mumford, *Tata I*, II §1; Birkenhake–Lange §8.5; numbering UNVERIFIED). The condition is independent of the sign
  convention for the Riemann form.

### 2.2 The new leaf `PazukiCor13UpperPP` (printed form)

```lean
def PazukiCor13UpperPP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
    ∀ (σ : K →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
      (φ : Torus Λ ≃+ Additive (CPts (bcC A σ) (RingHom.id ℂ))),
      BPAnalytic.Uniformization.IsUniformization (bcC A σ) Λ φ →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (L : (A.baseChange K').X.left.Pic),
      IsSymmPrincipal (A.baseChange K') L →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsThetaPeriodMatrix A σ σ' hσ L Λ φ Ω →
    ∀ (F : Type) [Field F] [NumberField F] (emb : F →+* ℂ) (z : Char2 → F) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      max 1 (absLogHeightL2 z) - max 1 (x + Real.log Real.pi) / 2 ≤
        pazukiC2 * Real.log (min (max 1 (absLogHeightL2 z)) (max 1 (x + Real.log Real.pi)) + 2)
```

**Rating: printed form**, flag *reading risk* (Def. 2.6 coordinates).
- **What the print says.** For a principally polarized abelian surface `(A, L)` over `ℚ̄`:
  `|H_Θ − H_D/2| ≤ C₂ log(min(H_Θ, H_D) + 2)`.
- **What the leaf is.** The upper half of that display, for the model `(A_{K'}, L)` of `(A, L)_ℚ̄`. The reading steps
  are the same as the existing field's (all already accepted for it):
  - `h_D = x + log π` (locators.md item 5);
  - the ℓ²-height of the theta-null point is Pazuki's theta height;
  - the stable height is invariant under `K'/K`;
  - the theta-null point does not depend on the symplectic basis.
- **What it no longer contains.**
  - The polarization is algebraic and principal: `IsSymmPrincipal`; `h⁰ = 1` for ample `L` means `deg φ_L = 1`
    (Riemann–Roch, Mumford §16).
  - `Ω` is the period matrix of that `L`.
  - The uniformization is the biholomorphic one, as in the print (bp-analytic's three clauses).
  - So neither the analytic-to-algebraic step nor the weak-uniformization step is in the leaf.
- **What remains a risk.** The identification of Pazuki's level-2 coordinates (Def. 2.6) with the classical
  `θ[a;b](0, Ω)` is UNVERIFIED (unchanged from the field, leaf-review-b premise 3). If his coordinates are
  `θ[a;0](0, 2Ω)`, the leaf overstates the print by about `log 4`.
- **Not stronger than the print.** Every hypothesis of the print is implied by the leaf's hypotheses:
  - `(A_{K'}, L)` is a principally polarized abelian surface over a number field;
  - `L` is symmetric (Pazuki works with symmetric `L`; the leaf assumes it);
  - `Ω` is its period matrix.

  The conclusion is the upper half of the printed display.

### 2.3 The remaining named Prop `AnalyticPPAlgebraic` (GLUE, composite)

```lean
def AnalyticPPAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ)) (φ : Torus Λ ≃+ Additive (CPts (bcC A σ) (RingHom.id ℂ))),
    BPAnalytic.Uniformization.IsUniformization (bcC A σ) Λ φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → ∀ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
      (∀ w, w ∈ Λ ↔ ∃ m n : Fin 2 → ℤ, T w = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)) →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (L : (A.baseChange K').X.left.Pic),
      IsSymmPrincipal (A.baseChange K') L ∧ IsThetaPeriodMatrix A σ σ' hσ L Λ φ Ω
```

**Why true** (STANDARD; locators UNVERIFIED). Take `c = 0`.
1. `θ(·, Ω)` spans `H⁰` of the line bundle of the principal Riemann form of `Ωℤ² + ℤ²` (Appell–Humbert and
   Frobenius; Mumford, *Abelian varieties*, §§2-3; Birkenhake–Lange §8.5). Its divisor is symmetric because `θ` is
   even.
2. By GAGA/Chow (Serre 1956; SGA 1 XII 4.4) the analytic divisor `φ(T⁻¹{θ = 0})` is an effective divisor `D` on
   `A_ℂ`. `𝒪(D)` is ample (Mumford §6, Application 1) and has `h⁰ = 1`.
3. `NS(A_ℚ̄) = NS(A_ℂ)` (Maulik–Poonen, Prop. 3.1, UNVERIFIED). Symmetric bundles in one class differ by `Pic⁰[2]`,
   whose points are `ℚ̄`-points. So `𝒪(D) ≅ L_ℂ` for a symmetric `L` on `A_{K'}`, `K' ⊂ ℂ` a number field over `σ`.
4. `H⁰` commutes with flat base change, so the section of `L` has divisor `D` on complex points. Ampleness and
   symmetry descend because `Pic(A_{K'}) → Pic(A_ℂ)` is injective.

**Rating: GLUE (composite).** It composes Appell–Humbert/Frobenius, GAGA, ampleness, NS invariance and the `Pic⁰[2]`
torsor; no single source states it. A printed form would need analytic line bundles on complex tori, which Mathlib
does not have.

**Finer split (optional; proved):**

```lean
theorem analyticPPAlgebraic_of_split (h1 : ThetaDivisorAlgebraicC) (h2 : SymmPrincipalDescends) :
    AnalyticPPAlgebraic
```

- `ThetaDivisorAlgebraicC` is the analytic half, over `ℂ`. For `B/ℂ` with biholomorphic `φ` and `(Ω, T)`, there are
  a symmetric principal `L` on `B`, a section `s` and a vector `c` with `φ(w) ∈ Z(s) ⟺ θ(Tw + c, Ω) = 0`. Sources:
  Appell–Humbert, Frobenius, GAGA. GLUE (composite).
- `SymmPrincipalDescends` is the arithmetic half. A symmetric principal `(L, s)` on `A_ℂ`, for `A` over a number
  field, comes from a symmetric principal `(L', s')` on some `A_{K'}` with the same divisor on complex points.
  Sources: NS invariance, `Pic⁰[2]`, flat base change. GLUE (composite).

The autofold spec uses the single composite, which adds one GLUE row instead of two. The integrator may prefer the
split.

## 3. Glue proved in Lean (VERIFIED, compiled, standard axioms)

| theorem | content |
| --- | --- |
| `specMap_comp_eq` | `Spec σ' ≫ Spec(K → K') = Spec σ` for `σ = σ' ∘ (K → K')` |
| `eq_zero_of_smul_mem` | if `T(Λ) = Ωℤ² + ℤ²` (`T` a `ℂ`-linear isomorphism), `Λ` contains no complex line, because `Ωℤ² + ℤ²` is countable |
| `toMul_proj_eq_one_iff` | `φ(proj w) = 1 ↔ w ∈ Λ` |
| `exists_strong_of_weak` | **the weak-to-biholomorphic step**, see below |
| `analyticPPAlgebraic_of_split` | the composite from its two halves |
| `pazukiCor13Upper_of_printed` | **the main theorem** |

**`exists_strong_of_weak`.** Let `Φ` be a weak uniformization at `(K, σ)` with kernel `Λ`, where `Λ` contains no
complex line. Then `Φ = ptE ∘ φ ∘ proj ∘ D`, where:
- `φ` is the biholomorphic uniformization of `A_ℂ`, from `UniformizationLeafAll`;
- `D : ℂ² ≃ ℂ^g` is a `ℂ`-linear **isomorphism**;
- `Λ = D⁻¹(Λ_B)`.

The proof has three steps:
1. **Lifting.** homlattice's `exists_complexLinear_of_analytic`, applied after av-split's `isAnalyticHom_ptE_symm`
   (infra-stalks' local structure of fibre products).
2. **`D` is onto.** homlattice's `surjective_of_proj_comp_surjective`.
3. **`D` is one-to-one.** Its kernel is a complex subspace inside `Λ`.

No dimension theory is needed. Injectivity uses only `IsPeriodMatrix`, through `eq_zero_of_smul_mem`.

**The main proof.** It has four steps:
1. `IsPeriodMatrix` gives `T`.
2. `exists_strong_of_weak` gives `(g, Λ_B, φ, D)`.
3. `T ∘ D⁻¹` carries `Λ_B` onto `Ωℤ² + ℤ²`. Then `AnalyticPPAlgebraic` gives `(K', σ', L)` with
   `IsThetaPeriodMatrix … Ω`.
4. `PazukiCor13UpperPP` gives the bound for the same `x`, `Ω`, `z`, `c`.

## 4. Checks

(Filled in below as they complete: full build, `#discharges`, autofold dry run.)
