# g0-mod-field: glue steps G2, G4, G7 (the field half of `ModularConstituent`)

Task g0-mod-field, 2026-11-13. Lean: `scratch/g0-mod-field/ModField.lean` (about 760 lines; it imports
`ZInQKernel/HDecomp/` modules and is not a flat copy). Log: `scratch/g0-mod-field/log.md`.

## 1. Result

**For every fibre context, G7's output follows from five glue Props and four leaves. All of it
is proved in Lean, with no `sorry`.** Composed with the next ranges (G8-G16, bundled as one Prop
`AfterG7`), this gives `ModularConstituent`. VERIFIED: `lake env lean scratch/g0-mod-field/ModField.lean`
gives 0 errors and no `declaration uses sorry`. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for `fieldDescent`, `fieldDescentUnr`, `descentDatum_of_conjugacy`, `g7Out_of_g4Out`,
`g7OutUnr_of_g4Out`, `modularConstituent_of_ranges`, `modularConstituent_of_ranges_T14` and
`galoisG2Out_of_g7Data`.

```
theorem G0ModField.fieldDescentUnr (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y Φ π u P) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P

theorem G0ModField.modularConstituent_of_ranges_T14 (hCover : FibreCoverExists)
    (hKer : KernelFieldExists) (hSup : UnramifiedSup) (hH : PkgI6.BrauerHasse2C)
    (hR : PkgI6.BrauerReciprocity2C) (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (hRest : AfterG7) : ModularConstituentG
```

The leaves are the bundle's T14a, T14b, T15 (pkg-I6's cochain forms; or glue-descent's
`LeafHasse`, `LeafLocalTwo` in the first theorem), T30 (`LeafSqrtCrit`) and T31
(`LeafUnramified`). Here `S = S_mul` and `R = D`, the instance `SixContactMin` uses.
`T = S_mul ∪ supp M_{S_mul}(u)`. The admissibility facts (`S_mul` consists of primes, every
prime of `S_mul` is `≤ D`, and `10¹² ≤ D`) are proved (`admissible_S_mul`, copied from
`ZInQKernel/Main.lean`).

### Outputs of the range (`def … : Prop`, each with a docstring)

| name | step | content |
|---|---|---|
| `FibreCtx Y Φ π u P` | input | the hypotheses of `ModularConstituent`: R1-R2 clauses, `u ∉ 𝒞`, a `ℚ̄`-point `y` with object `P` over `J(u)` |
| `IsModelOver L A P` | — | `A/L` (`L ⊆ ℚ̄`) is a model of `P`'s surface: `A_ℚ̄ ≅ P.A` as `ℚ̄`-schemes |
| `G2Out u P` | G2 | `K ⊆ ℚ̄` finite Galois, `[K:ℚ] ≤ 324!`, unramified outside `T`, a model of `P` over `K` |
| `DescentDatum L A ε` | B1 | `ε` a normalized locally constant sign cocycle inflated from `Gal(L/ℚ)`, with maps `m_σ = μ_σ∘σ` on `A(ℚ̄)` and reals `a_σ > 0` (see §2) |
| `G4Out u P` | G4 | Hom field `L` finite Galois, `[L:ℚ] ≤ D`, unramified outside `T`, model `A/L`, `DescentDatum L A ε` |
| `G7Out u P` | G7 | G4's data plus `χ`, `β` (`β² = χ`, `∂β = ε`) and `L' ⊇ L` with `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M`, `A_{L'}` a model |
| `G7Data u P L A ε N χ β L' h` | G7 | the same as a clause list, plus `N` supported on `T`, the twisted `β`, and `L'` unramified outside `T` (inertia form `GlueB3Unram.GalUnramifiedOutside`) |
| `G7OutUnr u P` | G7 | `∃` data with `G7Data` |

### Proved steps

| theorem | step | from |
|---|---|---|
| `g2Out_of_cover` | G2 bookkeeping | `FibreCoverOut`: a splitting field of a separable `f`, `deg f ≤ 324`, is Galois with `[K:ℚ] ≤ 324!` (`GlueRepo.Numerics.splitting_degree_le`) |
| `descentDatum_of_conjugacy` | B1 normalization (N5 L645-663) | `ConjugacyData`: `a_σ = \|ker m_σ\|^{-1/4}`, `ε = sgn c`; `a σ · a τ · c = ε · a(στ)` from `\|ker m_σ\|·\|ker m_τ\| = c⁴·\|ker m_{στ}\|`; cocycle identity and local constancy of `ε` (through `isLocallyConstant_of_openSubgroup` on `G_L × G_L`) |
| `g4Out_of_kernelField` | G4 bookkeeping (N5 L540-563) | `KernelFieldOut`: `[E⊔K:ℚ] ≤ F₀·3^{r²} ≤ D` (Minkowski `card_le_three_pow`, `a8_field`), `E ⊔ K` Galois, the model by base change, and B1 |
| `isModelOver_baseChange`, `baseChangeTrans` | — | `(A_{L'})_ℚ̄ ≅ A_ℚ̄` (Mathlib's `Over.pullbackComp`) |
| `b3_of_cochain` | B3 | glue-descent's `b3_of_leaves` proof with B2's cochain as a hypothesis, so that the twist can depend on it |
| `g7Out_of_g4Out` | G7 (B2-B3) | `GlueDescent.B3Q.b3_degree_le_QM` at `S_mul`, `D`, `η = 1` |
| `g7OutUnr_of_g4Out` | G7 with the twist (N5 L664-716) | `b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf` (B3(v), no leaf), `b3_of_cochain`, `degree_le_QM` |
| `fieldDescent`, `fieldDescentUnr` | G2 → G4 → G7 | the above |
| `modularConstituent_of_ranges(_T14)` | piece 10 | `fieldDescentUnr` and `AfterG7` |

### What remains (named Props), smallest first (sizes SPECULATIVE)

1. `UnramifiedSup`: a compositum of two finite Galois extensions of `ℚ`, both unramified at `p`,
   is unramified at `p`. STANDARD (Neukirch I §8; locator UNVERIFIED), but not in Mathlib v4.35.
   Small to medium.
2. `FibreCoverExists` (G2: Prop. TS + Lemma NV on the actual fibre). For each fibre context:
   a separable `f ∈ ℚ[X]` with `deg f ≤ 324`, whose splitting field `K ⊆ ℚ̄` is unramified
   outside `T` and carries a model of `P`. Proved inputs: the valuation case analysis
   `GlueRepo.PR.inertia_orders_eq_one_iff` and Lemma NV step 2. Missing: the degree theory of
   curves and the function-field Galois theory (leaf-qm-fp §4). Large.
3. `KernelFieldExists` (G4 + B1's geometric half). For each fibre context and each `K`, `A/K` as
   in G2's output, `KernelFieldOut u P K A`. This asks for: the rank `r ≤ 16F₀²` of the
   endomorphism lattice of `Res_{K/ℚ} A`; its Galois image, a finite `G ≤ GL_r(ℤ)`; the kernel
   field `E` with `[E:ℚ] = |G|`, unramified outside `T`; and `ConjugacyData` on `A_{E⊔K}`. The
   last is the maps `m_σ = μ_σ∘σ` with `μ_σ` the `B`-linear conjugacy isogenies (Skolem-Noether,
   which uses NoCM, G6), the rational discrepancy `c` and the kernel sizes. Medium-large. It
   needs Weil restriction, Tate modules of `W₀` and Skolem-Noether (T13,
   `GlueDescent.LeafSkolemNoether`, proved by t-skolem-kw per its report).
4. `AfterG7`: the ranges G8-G16, owned by g0-mod-galois and g0-mod-newform (§3). Connecting
   them to this range takes two bridge Props, `ResQRange` (Mathlib-level) and `TateBridge`
   (medium), both stated in Lean (§3).

## 2. The descent datum on the actual `A`

The maps are `m_σ : A(ℚ̄) → A(ℚ̄)`, additive maps on the `ℚ̄`-points (`PkgI3.AbVar.Pt`) of `A/L`.
Glazer's `μ_σ ∘ σ` acts on points and does not depend on `ℓ`. On `V_ℓ(A)`, they give G8's
`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` for every `ℓ` at once. `DescentDatum L A ε` asks:

* `0 < a_σ`; `a_k = 1`, `a_{σk} = a_{kσ} = a_σ` for `k ∈ G_L`;
* `m_σ` is the Galois action `PkgI3.AbVar.galAct σ'` for `σ ∈ G_L` (`σ'` is `σ` as an
  `L`-automorphism);
* `m_{σk} = m_σ m_k` and `m_{kσ} = m_k m_σ` for `k ∈ G_L`;
* `m_σ` commutes with `ptMap f` for every `f ∈ End_L(A)`;
* `m_σ` is surjective with finite kernel;
* `d·m_σ m_τ = n·m_{στ}` with `n, d ≠ 0` and `a_σ a_τ (n/d) = ε(σ,τ) a_{στ}`.

**Each clause is true for Glazer's data** (model check, no human review). `μ_σ` is inflated from
`Gal(L/ℚ)`, `μ_1 = 1`, and `μ_σ` is defined over `L`, which gives the `G_L` clauses. B-linearity
gives commutation with `End_L(A)`. Commutation with all of `End_L(A)` uses `End⁰_L(A) = B`,
true only off the CM locus. That is why `KernelFieldExists` is quantified over `FibreCtx`, which
contains `u ∉ 𝒞`. `μ_σ` is an isogeny, so it is surjective on `ℚ̄`-points with finite kernel.
The relation `c = n/d ∈ ℚ^×` holds because the discrepancy commutes with `B` (N5 L640-644,
`GlueDescent.B6_commute_i_j`). The `a`-identity is N5 L651-660. In `ConjugacyData`, the kernel
sizes are degrees: in characteristic 0, `deg μ = |ker μ(ℚ̄)|`, and on a surface `|A[n]| = n⁴`.

**One fix found and made (VERIFIED as a logical point).** The first draft did not constrain `a`
on `G_L`. That left `a` free up to a character `G_ℚ → ℝ_{>0}` (the identity
`a_σ a_τ c = ε a_{στ}` is invariant under `a ↦ aλ`). g0-mod-galois' `G7Out` asks for `a = 1` on
`G_{L'}`. The clauses `a_k = 1`, `a_{σk} = a_{kσ} = a_σ` were added, and B1's normalization
proves them from `|ker m_k| = 1`, `|ker m_{σk}| = |ker m_{kσ}| = |ker m_σ|`.

## 3. How the conclusion feeds the next range and `ModularConstituent`

**Into `ModularConstituent` (proved: `modularConstituent_of_ranges`).** The theorem takes
`G7Data`'s `L'` as `⟨L'⟩ : GlueAssembly.NF` (a number field by `numberField_of_fd`) and
`emb = algebraMap L' ℚ̄`. It takes the model as `A_{L'}`, the base change of `A/L` along
`incAlg hLL'`. Then `G7Data`'s ninth clause is `[L':ℚ] ≤ Q_D·M_{S_mul}(u)`, its eleventh is the
model clause (closed by defeq, since `emb.toAlgebra` and the intermediate-field instance give the
same `algebraMap`), and `AfterG7` gives `N`, `J₁(N)` and the common constituent.

`ModularConstituentG` is g0-split's `ModularConstituent` (scratch/g0-split/part_split.lean) with
two copies merged. `ZInQ.DefFaltings.AbVar` (def-faltings' copy) becomes `PkgI3.AbVar`, which
`ZInQKernel/HDecomp/Faltings/Models.lean` already uses. `LeafAdopt.abVarEquiv`, the identity on
the underlying scheme, is dropped. `CommonConstituent` is copied verbatim. At integration, either
state `ModularConstituent` over `PkgI3.AbVar`, as `HDecomp` does, or insert `abVarEquiv`. Both
are definitional (`abVarEquiv` is `{ X := A.X }` both ways).

**Into G8-G12 (g0-mod-galois, `scratch/g0-mod-galois/part_galois.lean`, read at 02:15).** Their
inputs are per `ℓ` over an abstract number field `K` (= `L'`), via `resQ K`:
* their `G2Out K T` (inertia at `p ∉ T` lies in `G_K`) follows from `G7Data`'s clause
  `GlueB3Unram.GalUnramifiedOutside L' (T u)` (inertia `I_w ≤ G_{L'}`). **Proved in Lean:**
  `galoisG2Out_of_g7Data`, from `G7Data` and the named Prop `ResQRange`. `ResQRange` says the
  image of their `resQ L' = Field.absoluteGaloisGroup.map` is `Fix(L')` for finite Galois `L'`. It is
  true for any choice of embedding of the algebraic closures, because `L'/ℚ` is normal. It is
  Mathlib-level Galois theory and is not proved here. Their definitions `resQ`, `Vb`, `tate`,
  `G2Out` and `G7Out` are copied verbatim into `G0ModField.GaloisCopy` (from wip/g0-mod-galois at
  20fa1287);
* their `G7Out A ℓ Tm c ε a β u` has the operators `Tm σ` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`, which are the
  Tate functor applied to `m_σ`. The bridge `G7Data → G0Galois.G7Out` is new glue (not done here).
  It needs four things: (i) `T_ℓ` of `A_L(ℚ̄)` and of `A_{L'}(\overline{L'})` identified (choice of
  `\overline{L'} ≅ ℚ̄` over `L'`); (ii) `c = n/d`, `a_σ` (algebraic: `|ker m_σ|^{-1/4}`), and `ε`, `β`
  (roots of unity) mapped into `ℚ̄_ℓ` by one embedding of the number field they generate;
  (iii) the matrix units of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)` from `End_{L'}(A)`, using `DescentDatum`'s
  commutation clause and rank 4 (A9/G6); (iv) continuity from inflation and glue-rho-cont. Their
  clauses `Tm = tate`, `a = 1`, `β = 1` on `G_{L'}` come from `DescentDatum` (`m_k = galAct`,
  `a_k = 1`) and `G_{L'} = G_L ∩ ker β`. `A.dim = 2` follows from `IsModelOver` with `DimBaseChange`
  (g0-split's `model_dim`). `rank End = 4` is G5-G6, outside this range. **Stated in Lean** as the
  Prop `TateBridge`: `G7Data` + `dim A_{L'} = 2` + `rank_ℤ End(A_{L'}) = 4` gives, for every
  prime `ℓ`, data with `GaloisCopy.G7Out (A_{L'}) ℓ`.
* G16 (g0-mod-newform) uses `[L':ℚ]` only through `N ≤ QM²`. The `G7Data` clause
  `(∀ q prime, q ∣ N → q ∈ T)` with `N` the modulus of `χ` serves the conductor bound G15
  (`β` is ramified only in `T` after the twist).

## 4. Checks

* **The remaining Props are true given Glazer's argument** (model check). The fibre of the
  normalized cover over `u` is finite étale of degree `≤ 324`, so it is `Spec ℚ[X]/(f)` with `f`
  separable. Its splitting field contains every residue field, and `y` factors through it with
  the given embedding into `ℚ̄`. `Y₃` is a fine moduli space (level 3), so `P` has a model over
  `K`. `KernelFieldOut`: Glazer's `E` with its image in `GL_r(ℤ)` (`r` can be taken `≤ 16F₀²`), and
  `ConjugacyData` as in §2.
* **No hypothesis is a disguised conclusion.** `G7Data`'s numerical clause
  `[L':ℚ] ≤ Q_D·M` is proved from `[L:ℚ] ≤ D`, the order of `χ` and glue-descent's constants. It
  is not assumed. `[L:ℚ] ≤ D` is proved from Minkowski's bound and `r ≤ 16F₀²`.
* **Pitfalls met (VERIFIED):** after `open MonObj`, `η` is a token, so a binder named `η` does not
  parse. `ZInQKernel.Main` cannot be imported by a scratch file in this tree (its upstream
  `ZInQ.*` helpers are not built), so `le_heightD_of_mem_S_mul` is copied. Building
  `ZInQKernel.Hypotheses.JHeight` once builds the helpers that other `HDecomp` imports need.
  The modules `HDecomp.QM.Leaves`, `B3Unram.T32a`, `I3Linalg.C2`, `ModCurves.Defs` and
  `Descent.WP3` had no oleans in this worktree and were built with `lake build`.

## 5. Integration

`ModField.lean` imports only `ZInQKernel/HDecomp/` modules plus `Hypotheses/JHeight`,
`Multiplication/Certificate/ConstantsProperties`, `Progressions/Final/Instance` and
`Size/Constants/T`. So it can become `ZInQKernel/HDecomp/ModField.lean` as it stands. Its
namespace is `G0ModField` and nothing in it is a copy except `CommonConstituent`,
`le_heightD_of_mem_S_mul` and `b3_of_cochain`. To close `G0Split.ModularConstituent` in
`Split.lean`, prove `AfterG7` (or replace it by the composite of g0-mod-galois' and
g0-mod-newform's theorems through the bridge of §3), then use `modularConstituent_of_ranges_T14`.
`MissingPieces.modularConstituent` is then replaced by `FibreCoverExists`, `KernelFieldExists`,
`UnramifiedSup` and `AfterG7`'s pieces.
