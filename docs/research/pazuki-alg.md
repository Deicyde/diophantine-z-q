# pazuki-alg: the analytic half of `AnalyticPPAlgebraic` from Riemann's theorem and GAGA for morphisms

Task pazuki-alg, 2026-11-16/17. Base wip/pazuki-dict 37b70108; origin/main (e41a7169) and
origin/wip/integrate-w82 (5e235a40) were merged first, both cleanly.

- Lean: `ZInQKernel/Contrib/OneProof/PazukiAlg.lean` (namespace `PazukiAlg`).
- Log: `scratch/pazuki-alg/log.md`.
- Autofold spec: `scratch/pazuki-alg/autofold.json`.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, reference given), **SPECULATIVE**.
Theorem numbers recalled without a source are **UNVERIFIED**: this host has no network and no copy of the books.
This is model work with no human review.

## 0. Verdict and main result

**The target (pazuki fold at −1 GLUE) is not met. `AnalyticPPAlgebraic` is not provable from what the fold has**
(`uniformizationLeafAll`, AbVar projectivity, `gagaMorphism`, gaga-serre's `SerreGAGAMorphism`). Two inputs are
missing (§1):

- **(a) The theta line bundle.** GAGA for *morphisms* only algebraizes maps. A map to `ℙ^N` (for instance a theta
  map) gives the pullback of `𝒪(1)`, which is `nΘ` with `n ≥ 2`. It never gives the line bundle of `Θ` itself,
  which is the one with `h⁰ = 1`. Getting `Θ` needs GAGA for line bundles (or Weil divisors and Riemann–Roch), and
  neither can be stated in Lean today.
- **(b) The descent from `ℂ` to a number field.** No field of the fold descends a line bundle from `A_ℂ` to
  `A_{K'}`. This needs `NS(A_ℚ̄) = NS(A_ℂ)`.

**What was done instead (VERIFIED, compiled, axioms below): the analytic half is reduced to one classical statement
about `Ω` alone, with every other step proved in Lean.** pazuki-dict split `AnalyticPPAlgebraic` (proved there)
into two parts:

- the analytic half `ThetaDivisorAlgebraicC`, about a given complex abelian variety `B`;
- the arithmetic half `SymmPrincipalDescends`.

This task proves

```lean
theorem PazukiAlg.thetaDivisorAlgebraicC_of_riemann (hR : RiemannPPAV) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hT : SymmPrincipalTransport) : PazukiDict.ThetaDivisorAlgebraicC
theorem PazukiAlg.symmPrincipalTransport : SymmPrincipalTransport
theorem PazukiAlg.pazukiCor13Upper_of_riemann (hG : ZInQ.HomLattice.GAGAMorphism)
    (hP : PazukiDict.PazukiCor13UpperPP) (hR : RiemannPPAV) (hD : PazukiDict.SymmPrincipalDescends) :
    ZInQ.HeightSplit.PazukiCor13Upper
```

- **`RiemannPPAV` (new).** Riemann's theorem for `Ω ∈ 𝔥₂`: `ℂ²/(Ωℤ² + ℤ²)` is a principally polarized abelian
  surface whose theta divisor is the zero set of `θ(· + c, Ω)`. It is stated about `Ω` only: no `A`, no number
  field. This is the "algebraicity of a polarized complex torus" that the task suggested.
- **`gagaMorphism`.** The existing textbook field, applied twice to get an isomorphism `B ≅ B₀` of abelian
  varieties that is compatible with the uniformizations.
- **`SymmPrincipalTransport`.** The pullback of a symmetric principal polarization along an isomorphism of abelian
  varieties. It is **proved** in Lean: ampleness, symmetry, `h⁰` and the divisor are all transported.
- **`uniformizationLeafAll`.** A theorem since PR #35 (`uniformizationLeafAll_proof`).

The arithmetic half `SymmPrincipalDescends` stays a composite GLUE. **Count:** see §4.

No statement was changed. None of the statements is false or vacuous (§2.3).

## 1. Why the fold's inputs do not suffice (VERIFIED by reading the statements)

- **`GAGAMorphism`** (`ZInQKernel/OneProof/H/TailQ.lean:875`): for a strong uniformization
  `φ : ℂ^g/Λ ≃ A(ℂ)` and an analytic homomorphism `ψ : ℂ^g → B(ℂ)` killing `Λ`, there is a morphism
  `f : A.X ⟶ B.X` inducing `ψ`. Its output is a morphism of abelian varieties and nothing else.
- **`SerreGAGAMorphism`** (gaga-serre; not on main: `origin/wip/gaga-serre` is not an ancestor of HEAD) makes
  holomorphic maps between projective varieties regular. With it, the classical theta maps
  `z ↦ [θ[a/n; 0](nz, nΩ)]_a` become algebraic morphisms `A_ℂ → ℙ^N`. The line bundles obtained are pullbacks of
  `𝒪(1)`, i.e. `nΘ` with `n ≥ 2` (`h⁰ = n^g`). `IsThetaPeriodMatrix` together with `IsSymmPrincipal` (`h⁰ = 1`)
  requires the line bundle of `Θ` itself. Extracting it from `nΘ` needs Weil divisors on a smooth variety and
  Riemann–Roch, or GAGA for line bundles. Mathlib and the project have neither, and there are no analytic line
  bundles to state GAGA over.
- **`exists_closedImmersion_projectiveSpace`** (projectivity) and `uniformizationLeafAll` give embeddings and
  uniformizations, not line bundles with prescribed sections.
- **Descent.** `AnalyticPPAlgebraic` asks for `L` on `A_{K'}` for a number field `K'`. Whatever the analytic step
  produces lives on `A_ℂ`. The fold's Pic fields (`picRepresentableAbVar`, `picZeroAbVar`, `mumfordPhiSurjectiveAC`,
  …) are statements over one field. None compares `Pic(A_ℂ)` with `Pic(A_{ℚ̄})`, which is the Néron–Severi
  invariance under extension of algebraically closed fields.
- **The consumers.** `AnalyticPPAlgebraic` is consumed only by `PazukiDict.pazukiCor13Upper_of_printed` (grep of
  the tree). It is already restricted to complex tori that come from an abelian variety's period lattice:
  `Λ, φ` are a uniformization of `A_σ`, with `A` over a number field. That restriction is exactly what makes the
  descent (b) necessary. For `Ω` alone, without `A`, no ℚ̄-model exists in general.

## 2. The statements

### 2.1 Verbatim target

`scratch/pazuki-alg/Verbatim.lean` copies `PazukiDict.AnalyticPPAlgebraic` (from
`ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean`, as at 37b70108) and checks it `rfl` against the original
(result in §3).

### 2.2 New leaf `RiemannPPAV`

```lean
def periodLattice (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Submodule ℤ (Fin 2 → ℂ)   -- carrier {Ωm + n}

def RiemannPPAV : Prop :=
  ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω →
    ∃ (B₀ : PkgI3.AbVar ℂ) (φ₀ : Torus (periodLattice Ω) ≃+ Additive (B₀.Pt ℂ)),
      BPAnalytic.Uniformization.IsUniformization B₀ (periodLattice Ω) φ₀ ∧
      ∃ (L₀ : B₀.X.left.Pic)
        (s₀ : 𝟙_ B₀.X.left.Modules ⟶ (fromSkeleton B₀.X.left.Modules).obj L₀.val),
        ∃ c : Fin 2 → ℂ, IsSymmPrincipal B₀ L₀ ∧
        ∀ v : Fin 2 → ℂ, OnZeroLocus s₀ (Additive.toMul (φ₀ (proj (periodLattice Ω) v))).left ↔
          riemannTheta Ω (v + c) = 0
```

Every object is an existing genuine definition:

- `PkgI3.AbVar` and bp-analytic's biholomorphic `IsUniformization`;
- the vendored `Scheme.Pic` and `zeroLocus`;
- t09-pic's `IsAmple` (through pazuki-dict's `IsSymmPrincipal`);
- pazuki-dict's `riemannTheta`, a `tsum`.

**Rating: composite (GLUE); not printed form.**

- **What the print says.** In the analytic category (Mumford, *Abelian varieties*, §§2-3; Mumford, *Tata Lectures on
  Theta I*, Ch. II §§1, 3; Birkenhake–Lange §8.1 and §8.5; numbering UNVERIFIED):
  - `X_Ω = ℂ^g/(Ωℤ^g + ℤ^g)` with `H_Ω = (Im Ω)⁻¹` is a principally polarized abelian variety;
  - `θ(·, Ω)` spans `H⁰` of the symmetric line bundle `L(H_Ω, χ₀)`, which is ample.
- **What the Lean statement adds.** It speaks of a scheme `B₀` and an algebraic `L₀`. That reading passes through
  Chow's theorem (`X_Ω` is projective, Lefschetz) and GAGA (the line bundle and its section are algebraic). This
  follows the 11-16 dictionary precedent (the uniformization leaf, "Mumford §1 applied to `A^an`", was a
  consequence).
- **What would clear it.** A print of the scheme form. Mumford §3 may contain it ("X is an abelian variety; by GAGA
  every analytic line bundle is algebraic"), but that is UNVERIFIED (not read).
- **Not stronger than the print.**
  - The existential over `c` only weakens it: the print has `c = 0`, and the `c` makes the statement independent of
    the characteristic convention of the symmetric bundle.
  - `IsSymmPrincipal` is the print's "symmetric, ample, `h⁰ = 1`" (Frobenius: `h⁰(L(H, α)) = √det E = 1`).
  - The biholomorphic `IsUniformization` is the coordinate form of `X_Ω ≅ B₀^an`.

### 2.3 Consistency of the leaf (VERIFIED, proved)

`RiemannPPAV` compares a condition on `proj v ∈ ℂ²/(Ωℤ² + ℤ²)` with `θ(v + c, Ω) = 0`. It would be false as stated
if the zero set of `θ` were not `Ωℤ² + ℤ²`-periodic, so the file proves that periodicity, with no convergence
needed (the proofs reindex the `tsum`):

- **`riemannTheta_add_int`:** `θ(z + n, Ω) = θ(z, Ω)` for `n ∈ ℤ²`.
- **`riemannTheta_add_period`:** `θ(z + Ωm, Ω) = exp(−πi mᵀΩm − 2πi mᵀz) θ(z, Ω)` for `Ω` symmetric.
- **`riemannTheta_add_mem_eq_zero_iff`:** the zero set is invariant under `Ωℤ² + ℤ²`.

`RiemannPPAV` is true (STANDARD, the classical theory above). It is not vacuous: `𝔥₂ ≠ ∅` (`isSiegel_I` in the
kernel).

### 2.4 Glue Prop `SymmPrincipalTransport` (proved)

```lean
def SymmPrincipalTransport : Prop :=
  ∀ (B B₀ : PkgI3.AbVar ℂ) (u : B.X ⟶ B₀.X) [IsIso u], u ≫ GrpObj.inv = GrpObj.inv ≫ u →
    ∀ (L₀ : B₀.X.left.Pic)
      (s₀ : 𝟙_ B₀.X.left.Modules ⟶ (fromSkeleton B₀.X.left.Modules).obj L₀.val),
      IsSymmPrincipal B₀ L₀ →
      ∃ (L : B.X.left.Pic) (s : 𝟙_ B.X.left.Modules ⟶ (fromSkeleton B.X.left.Modules).obj L.val),
        IsSymmPrincipal B L ∧
        ∀ q : Spec (CommRingCat.of ℂ) ⟶ B.X.left, OnZeroLocus s q ↔ OnZeroLocus s₀ (q ≫ u.left)
```

### 2.5 Remaining GLUE: `SymmPrincipalDescends` (pazuki-dict's statement, unchanged)

This is the arithmetic half: a symmetric principal `(L, s)` on `A_ℂ` is the base change of one on `A_{K'}`.

- **Rating: composite (GLUE).** Its ingredients are:
  - `NS(A_ℚ̄) = NS(A_ℂ)` (Maulik–Poonen, Prop. 3.1, UNVERIFIED);
  - the symmetric bundles in one class form a torsor under `Pic⁰[2]`, whose points are `ℚ̄`-points;
  - flat base change of `H⁰` and descent of ampleness.
- **Why it was not reduced further in Lean.** Any finer split still contains the Néron–Severi step, which is not one
  printed theorem over the project's definitions. The base-change glue (injectivity of `Pic(A_{K'}) → Pic(A_ℂ)`,
  `H⁰` under field extension, descent of ampleness) has no infrastructure in Mathlib or the vendored libraries
  (searched: no such lemmas under `ZInQKernel/` or Mathlib's `AlgebraicGeometry/`). A finer split would only add
  GLUE rows.

## 3. Lean (VERIFIED, compiled; `ZInQKernel/Contrib/OneProof/PazukiAlg.lean`)

| theorem | content |
| --- | --- |
| `discreteTopology_periodLattice` | `Ωℤ² + ℤ²` is discrete for `Ω ∈ 𝔥₂`: `Im(Ωm + n) = (Im Ω) m` and `Im Ω` is invertible. GAGA's hypothesis `[DiscreteTopology Λ]` needs this. |
| `riemannTheta_add_int`, `riemannTheta_add_period`, `riemannTheta_add_mem_eq_zero_iff` | the functional equation of `θ` and the periodicity of its zero set (§2.3) |
| `tensorPowPullbackIso` | `(f^*M)^{⊗n} ≅ f^*(M^{⊗n})` (pullback is monoidal, vendored `pullbackMonoidal`) |
| `support_zeroLocus_pullbackSec` | the divisor of a pulled-back section is the preimage (vendored `comap_zeroLocus`, Mathlib `support_comap`) |
| `isAmple_map` | `IsAmple` transports along an isomorphism of schemes |
| `finrank_map` | `h⁰` transports along an isomorphism: pullback of global sections is bijective (`bijective_pullbackUnit_app_of_isOpenImmersion`) and semilinear over `f^* : Γ(Y) ≃ Γ(X)` (`rank_eq_of_equiv_equiv`) |
| `symmPrincipalTransport` | `SymmPrincipalTransport`: ampleness, symmetry (`Pic.map_comp`), `h⁰`, divisor |
| `thetaDivisorAlgebraicC_of_riemann` | **the analytic half** (below) |
| `analyticPPAlgebraic_of_riemann` | `AnalyticPPAlgebraic` from `RiemannPPAV`, `GAGAMorphism`, `SymmPrincipalDescends` |
| `pazukiCor13Upper_of_riemann` | **the field**, from `PazukiCor13UpperPP`, `RiemannPPAV`, `GAGAMorphism`, `SymmPrincipalDescends` |

**Proof of `thetaDivisorAlgebraicC_of_riemann`.** The input is `B` with biholomorphic `φ : ℂ^g/Λ ≃ B(ℂ)` and `T` with
`T(Λ) = Ωℤ² + ℤ²`.

1. `RiemannPPAV` gives `(B₀, φ₀, L₀, s₀, c)`.
2. `Λ = T⁻¹(Ωℤ² + ℤ²)` is discrete, because `w ↦ Tw` is a continuous injection into a discrete group.
3. GAGA applied to `φ₀ ∘ proj ∘ T` with source `B` gives `h : B → B₀`. The map is analytic by `isAnalyticHom_lin`
   and kills `Λ`. GAGA applied to `φ ∘ proj ∘ T⁻¹` with source `B₀` gives `f : B₀ → B`.
4. `h ≫ f` and `f ≫ h` are the identity on complex points, hence identities (hom-unify's `hom_ext_of_cpts`).
5. `h` commutes with the inverse maps, again on complex points.
6. `SymmPrincipalTransport` pulls `(L₀, s₀)` back along `h`. The divisor condition becomes
   `θ(Tw + c, Ω) = 0`, because `φ(proj w) ≫ h = φ₀(proj(Tw))`.

**Checks.** (Results recorded in `scratch/pazuki-alg/log.md`.)

- `lake env lean ZInQKernel/Contrib/OneProof/PazukiAlg.lean`: see §5.
- `#discharges`: see §5.
- Verbatim `rfl` check: see §5.
- Autofold dry run: see §5.

## 4. Fold count

Before the fold, kinds.tsv rates `pazukiCor13Upper` GLUE (the 11-16 re-rating). The spec
`scratch/pazuki-alg/autofold.json` discharges it with three leaves:

| leaf | kind | strict |
| --- | --- | --- |
| `pazukiCor13UpperPP` | published (pazuki-dict; printed form, reading risk Def. 2.6) | LEAF |
| `riemannPPAV` | composite (new) | GLUE |
| `symmPrincipalDescends` | composite (pazuki-dict) | GLUE |

**Net +1 GLUE** (needs `--allow-rise`). pazuki-dict's coarser spec, `PazukiCor13UpperPP` plus the single composite
`AnalyticPPAlgebraic`, is neutral.

The finer spec costs one row but buys three things:

- The analytic composite becomes a statement about `Ω` alone. It is the classical theorem a formalizer of complex
  abelian varieties would prove first: Appell–Humbert, Frobenius, Lefschetz and GAGA for `ℂ^g/Λ_Ω`.
- Everything between that theorem and the field is proved.
- The arithmetic composite is isolated as purely algebraic.

If a reading finds the scheme form of Riemann's theorem in print, `riemannPPAV` becomes LEAF and the fine fold is
neutral. A Lean proof of `SymmPrincipalDescends` would then give the −1.

## 5. Check results

(filled in below as the runs complete)
