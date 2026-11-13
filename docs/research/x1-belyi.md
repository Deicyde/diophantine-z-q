# x1-belyi: `X1ModelExists` and `BelyiX1` from five literature leaves

Task x1-belyi, 2026-11-12. Nodes MC4, MC5 and MC10 of `docs/research/bp-modcurves.md`. Lean file:
`scratch/x1-belyi/X1Belyi.lean` (imports `ZInQKernel.HDecomp.ModCurves.Glue`). Results log:
`scratch/x1-belyi/log.md`.

## Main result

Both glue targets of `ZInQKernel/HDecomp/ModCurves/Leaves.lean` are now Lean theorems. The
definitions are imported from the kernel, not restated. The proofs use five leaves, each a
`def … : Prop` over Mathlib definitions:

```lean
theorem X1Belyi.belyiX1_of_leaves (hT : TorsionStructure) (hG : GoodReductionUnramified) :
    LeafModCurves.BelyiX1
theorem X1Belyi.x1ModelExists_of_leaves (hT : TorsionStructure) (hC : CurveOfFunctionFieldQ)
    (hK : X1ConstantField) (hR : X1RationalCusp) : LeafModCurves.X1ModelExists
theorem X1Belyi.x1ModelExists_and_belyiX1 (L : X1Leaves) : X1ModelExists ∧ BelyiX1
theorem X1Belyi.modCurveLeaves_of (L : X1Leaves) (hJ : JacobianExists ℚ)
    (h16 : R16_EichlerShimuraJ1') (hd : DimJ1Genus) : ModCurveLeaves
```

Status: VERIFIED (compiled with `lake env lean scratch/x1-belyi/X1Belyi.lean`, no errors, no
`sorry`). `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all four theorems and
for `finrank_fieldX1_le`.

With this file, the field `x1 : X1ModelExists` of `ModCurveLeaves` is no longer a glue target.
It is replaced by the five leaves below (two of them, T1 and M1, are general textbook theorems not
specific to modular curves).

## Which steps need new leaves

| Step | What it says | Status |
|---|---|---|
| MC5, degree | `[ℚ(j)(x(P)) : ℚ(j)] ≤ N²` when `N • P = 0` | **proved** (`finrank_fieldX1_le`) from leaf **T1**. Proof: the conjugates of `x(P)` over `ℚ(j)` are the `x(σP)`, with `σP ∈ E[N]` and `#E[N] = N²`. Uses `Normal.minpoly_eq_iff_mem_orbit` and `card_rootSet_eq_natDegree` |
| MC5, transcendence | `j/1728` is transcendental over `ℚ` in `K_N` | **proved** (no leaf) |
| MC5, unramified outside `0, 1728, ∞` | `q(t)` generates `𝔪_w` at every place `w` over `q ≠ T, T − 1`, with `t = j/1728` | **proved** from leaf **T2**. The glue rewrites the place `q(t)` as the irreducible polynomial `p = q(T/1728)` of `ℚ[j]` (`scaleEquiv`, an automorphism of `ℚ[T]`), proves `p ∤ j²(j − 1728)⁹` (`scale_not_dvd`), and checks that Mathlib's `E_j` has good reduction at `p` (coefficients in `ℚ[j]`, `Δ = j²(j − 1728)⁹`) |
| MC4, smooth proper model with function field `K_N` | relative normalization of `ℙ¹_j` in `K_N` | **new leaf M1** (curves and function fields over `ℚ`) **plus new leaf M2** (`ℚ` is algebraically closed in `K_N`, which gives geometric connectedness) |
| MC10, a `ℚ`-point | a rational cusp | **new leaf M3** (`K_N` has a place of degree 1) plus the rational-point clause of M1 (closed points correspond to places, with the same residue fields) |
| a point `P` of exact order `N` exists | needed so that `IsX1Model` can be inhabited | **proved** (`exists_addOrderOf`) from leaf T1, as the image of `(1, 0)` |

So the steps that need new leaves are: smooth projective models of function fields of
transcendence degree one (M1, as the task suggested), the constant field of `K_N` (M2), a rational
cusp (M3), the structure of `E[N]` (T1), and Néron–Ogg–Shafarevich (T2). Everything else is glue
and is now proved.

## The leaves (`scratch/x1-belyi/X1Belyi.lean`)

All theorem numbers below are from memory and are UNVERIFIED (no network).

* **T1 `TorsionStructure`.** For an elliptic curve `W` over an algebraically closed field `K` of
  characteristic 0 and `N ≥ 1`, `Nonempty (nTors W N ≃+ ZMod N × ZMod N)`, where `nTors W N` is
  the subgroup `{P | N • P = 0}` of `W.toAffine.Point`. Source: Silverman, *AEC*, Cor. III.6.4(b),
  specialized to characteristic 0. STANDARD.
* **T2 `GoodReductionUnramified`.** Let `k` be a field of characteristic 0, `W` elliptic over
  `k(T)`, and `p ∈ k[T]` irreducible. Suppose the coefficients of `W` are `p`-integral and
  `Δ = b/c` with `p ∤ b` and `p ∤ c`. Let `P` be a torsion point over `\overline{k(T)}`. Then every
  valuation subring `w` of `k(T)(x(P))` that contains `k[T]` and has `p ∈ 𝔪_w` satisfies
  `𝔪_w = p·w`. Source: Néron–Ogg–Shafarevich in the form of Serre–Tate, Ann. of Math. 88 (1968),
  Thm 1, which holds for any discretely valued field: good reduction implies that inertia acts
  trivially on `E[m]` for `m` prime to the residue characteristic (here the residue characteristic
  is 0). Silverman *AEC* VII.4.1 gives the complete case. The step "inertia acts trivially on
  `E[N]` ⇒ ramification index 1 at every place of `k(T)(x(P))` above `p`" is the
  fixed-field-of-inertia characterization (Serre, *Local Fields*, I §7). So the leaf is a
  consequence of two published statements, specialized to `k(T)`.
* **M1 `CurveOfFunctionFieldQ`.** Let `F` be a finite extension of `ℚ(T)` in which `ℚ` is
  algebraically closed. Then there is `X : Over SpecQ` with `IsCurve X` (proper, smooth of
  relative dimension 1, geometrically connected), `X.left` integral and
  `X.left.functionField ≃+* F`; and if `F` has a place of degree 1, then `X` has a `ℚ`-point.
  Source: Stacks Project, *Algebraic Curves*, the section on curves and function fields (normal
  projective model; closed points correspond to the nontrivial valuation rings of `F/k`, with the
  same residue fields). Also used: normal of dimension 1 over a perfect field ⇒ smooth, and
  `H⁰(X, 𝒪_X)` is the algebraic closure of `k` in `F`. Hartshorne I.6 and II.6.7 cover
  algebraically closed `k`. Specialized to `k = ℚ`. STANDARD; Stacks tags UNVERIFIED.
* **M2 `X1ConstantField`.** For `P` of exact order `N`, `ℚ` is algebraically closed in
  `K_N = ℚ(j)(x(P))`. Source: Igusa 1959; Shimura 1971 §6.2 (Prop. 6.9: `Gal(k_N/ℚ(j)) ≅
  GL₂(ℤ/N)/±1` with constant field `ℚ(ζ_N)`; the stabilizer of `±P` has surjective determinant, so
  its fixed field has constant field `ℚ`). UNVERIFIED numbers. This is the geometric
  irreducibility of `X₁(N)` over `ℚ` (MC1' of bp-modcurves).
* **M3 `X1RationalCusp`.** For `P` of exact order `N`, `K_N` has a place of degree 1 over `ℚ`.
  Justification: on the Tate curve over `ℚ((q))`, `q^{1/N}` has exact order `N` and
  `x(q^{1/N}) = q^{1/N} + 2q^{2/N} + …` generates `ℚ((q^{1/N}))`. That extension is totally
  ramified over `j = ∞` with residue field `ℚ`. Every point of exact order `N` is conjugate to
  `±q^{1/N}` over `\overline{ℚ}(j)` (Igusa: geometric monodromy contains `SL₂(ℤ/N)`), so all the
  fields `K_N` are `ℚ(j)`-isomorphic. Sources: Silverman, *Advanced Topics*, Ch. V (Tate curve);
  Ogg 1973 (rational cusps). UNVERIFIED. Alternative: state it as Shimura's canonical model with a
  rational cusp (MC9 of bp-modcurves).

Faithfulness checks (by reading the statements; no model review yet):
* None of the leaves quantifies over a structure invented for the purpose. The objects are
  Mathlib's `WeierstrassCurve`, `Affine.Point`, `RatFunc`, `ValuationSubring`,
  `IntermediateField.adjoin` and `Scheme`, plus the kernel's `IsCurve`, `RatPt`, `EjBar` and
  `fieldX1`.
* T2 is not stronger than NOS. The hypotheses `k[T] ⊆ w` and `p ∈ 𝔪_w` force `w ∩ k(T) =
  k[T]_(p)`. `w` is then a DVR, because `k(T)(x(P))/k(T)` is finite, so "unramified" is exactly
  `𝔪_w = p·w`. The condition on `Δ` asks for both `p ∤ b` and `p ∤ c`, which makes it a `p`-adic
  unit explicitly.
* M2 and M3 are stated for every `P` of exact order `N`. Because all such `P` are conjugate up
  to sign (Igusa), this is equivalent to the statement for one `P`.

## Supporting computation

`scratch/x1-belyi/divpoly_check.py` (PARI `elldivpol`; VERIFIED computed, `N ≤ 7` only). For
Mathlib's `E_j`, `disc = j²(j − 1728)⁹`. For `N = 2..7`, the polynomial of x-coordinates of points
of exact order `N` is irreducible over `ℚ(j)`, of degree 3, 4, 6, 12, 12, 24. For `N ≥ 3` these
equal `μ = [SL₂(ℤ) : ±Γ₁(N)]`, which is at most `N²`. Its x-discriminant is supported on
`{j, j − 1728}`. This is consistent with T2 (étale over every other finite place), with the degree
bound, and with M2/M3's transitivity (one Galois orbit).

## Findings

1. **Mathlib's `E_j` changed** (VERIFIED, read in `Mathlib/AlgebraicGeometry/EllipticCurve/
   ModelsWithJ.lean`). In Mathlib 4.35, `ofJNe0Or1728 j = ⟨j − 1728, 0, 0, −36(j − 1728)³,
   −(j − 1728)⁵⟩` with `Δ = j²(j − 1728)⁹`. The docstring of `LeafModCurves.Ej`
   (`ZInQKernel/HDecomp/ModCurves/Defs.lean`) describes the older model
   `y² + xy = x³ − 36/(j−1728)x − 1/(j−1728)`. The definition itself is correct, because it is
   Mathlib's; only the comment is stale (this task does not edit ZInQKernel). The polynomial model
   makes good reduction away from `j = 0, 1728` immediate.
2. Mathlib 4.35 has division polynomials (`ΨSq`, `Φ`, degrees) but no formula for `[n]P`, and no
   structure theorem for `E[N]`. That is why the degree bound goes through T1 rather than through
   `ψ_N²(x(P)) = 0`.
3. `IsBelyiFunction` (kernel) constrains only the finite places other than `t = 0, 1`. The
   unramifiedness at those places is all that `BelyiX1` asks for; the place `∞` is the third
   branch point.

## What remains

* All five leaves are formalization targets (for the crowdsourcing list):
  - T1 depends on the division-polynomial multiplication formula (David Angdinata's Mathlib
    project).
  - T2 needs formal groups, or the discriminant of `ψ_N`.
  - M1 is the largest: it needs properness and smoothness of the normalization of `ℙ¹` in `F`,
    built on Mathlib's relative normalization `Scheme.Hom.normalization`.
  - M2 and M3 need Igusa's theorem and the Tate curve, or Shimura's canonical model (MC9).
* Integration (after the announcement): copy `X1Belyi.lean` to
  `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean`. Then add `X1Leaves` to the leaf list of
  `h-decomposition.md` in place of the glue target `X1ModelExists`, and fold `BelyiX1` into the
  E2/R18 consumers.
* No human review of the leaf statements yet (one model review, below).

## Model review (2026-11-12, one independent subagent read; no Lean run)

The review found no leaf that is false, vacuous or stronger than what is published. Its rating
of each leaf:
* TorsionStructure: OK.
* CurveOfFunctionFieldQ: OK.
* GoodReductionUnramified: OK with caveat. The reviewer confirmed the claims made above:
  - `w ∩ k(T) = k[T]_(p)`, and `w` is a DVR by `[Γ_w : Γ_v] ≤ [L : k(T)]`, so `𝔪_w = p·w` is
    exactly `e = 1`;
  - the extra steps are the fixed field of inertia and the passage to the completion.
* X1ConstantField: OK with caveat. Shimura states it for Weber functions, but here
  `x' = x + (j−1728)²/12` differs from `x` by an element of `ℚ(j)`, so the field is the same.
  The reviewer checked `N = 1, 2, 3` by hand.
* X1RationalCusp: OK with caveat.
  - Proof sketch: `x(q^{1/N}) ∈ ℚ[[q^{1/N}]]`; a quadratic twist does not change
    `ℚ((1/j))(x)`; Igusa's transitivity then gives the claim for every `P`.
  - The reviewer checked `N = 2, 3, 4, 6` by hand.
  - Ogg's paper is model-specific, so the citation route is Igusa plus the Tate curve.
