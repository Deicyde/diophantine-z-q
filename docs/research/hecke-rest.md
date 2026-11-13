# hecke-rest: the four glue Props left by ts-hecke under `CoverModelOfHecke`

Task hecke-rest, 2026-11-13. Base: wip/hecke-rest (b7cdba8e) with origin/wip/ts-hecke merged.

The targets are the four glue inputs of ts-hecke's composite `TSHecke.coverModelOfHecke_of_tsHecke`
(scratch/ts-hecke/TSHecke.lean; docs/research/ts-hecke.md §8):

- `CurveGaloisChart`: ts-hecke already reduced it to `CurveNormChart`, so `CurveNormChart` is the
  target here;
- `CurveChartInf`;
- `HeckeFibreSizes`;
- `HeckeNoVertRam`.

All four are copied verbatim and none was changed.

Model work only; no human has reviewed it. Marks used throughout:

- **VERIFIED**: compiled, computed, or read in a named file.
- **STANDARD**: a published result, with its reference.
- **SPECULATIVE**: an assessment.
- **UNVERIFIED**: a locator recalled from memory (there is no network here).

## 1. Main result

**All four targets are true and reduced in Lean. One of them, `HeckeFibreSizes`, is proved from
three new leaves.** Everything compiles with standard axioms only (VERIFIED).

```lean
theorem HeckeRestAll.coverModelOfHecke_of_heckeRest (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hP : HeckeRestCurve.ChartProper) (hQ : HeckeRestCurve.ChartQuasiFinite)
    (hD : HeckeRestCurve.ChartDominant) (hFF : HeckeRestCurve.InfFnField)
    (hV : HeckeRestNV.HeckeVertWitness) : CoverModelOfHecke
```

There is also the analogous `HeckeRestAll.propTSAll_of_heckeRest`, which goes through prop-ts-glue's
`propTSAll_final`.

| Target | Compiled reduction | What remains |
|---|---|---|
| `HeckeFibreSizes` | `HeckeRest.heckeFibreSizes_of : TorsionStructure → QMAutCard → SerreRigidity3 → ALFixedPoints → HeckeFibreSizes` (with `M = 144`) | three **leaves** on QM pairs (§2) |
| `CurveNormChart` (hence `CurveGaloisChart`) | `HeckeRestCurve.curveNormChart_of_charts : ChartProper → ChartQuasiFinite → ChartDominant → CurveNormChart` | three glue Props of curve theory (§4) |
| `CurveChartInf` | `HeckeRestCurve.curveChartInf_of_charts : ChartProper → ChartQuasiFinite → ChartDominant → InfFnField → CurveChartInf` | the same three, plus `InfFnField` (§4) |
| `HeckeNoVertRam` | `HeckeRestNV.heckeNoVertRam_of_witness : HeckeVertWitness → HeckeNoVertRam` | `HeckeVertWitness`: one unramified vertical prime. This is **equivalent** to the target, not weaker (§3) |

**Proved along the way, with no hypotheses:**

- `ChartNormal` and `ChartNormalD` (sections of smooth curves are normal);
- `CurveSectionsDomain`;
- the level-structure count `lvEquiv : Good ≃ Level3 P.q` (72 level structures);
- Galois transitivity of ramification over a non-Dedekind base (`ramIdx_eq_of_under_eq`);
- `ℚ(X) = Frac ℤ[X]` (`isFractionRing_int`).

### Lean files (VERIFIED: `lake env lean`, 0 errors)

All four files are assembled by `scratch/hecke-rest/assemble.py` from verbatim line ranges.

| File | Contents | Time |
|---|---|---|
| `FibreSizes.lean` | aut-o-finite + Units + the target, then Part 1 | ~20 s |
| `NoVert.lean` | prop-ts prefix + the target, then Part 2 | ~15 s |
| `CurveChart.lean` | prop-ts prefix + image-plane value calculus + infra-smooth-dim/curve-glue copies + the targets, then Part 3 | ~35 s |
| `HeckeRestAll.lean` | all of `TSHecke.lean` (7109 lines) + the three new parts + the composite | 46 s |

- All 14 `#print axioms` lines of the new declarations read `[propext, Classical.choice, Quot.sound]`.
- The token `sorry` occurs only in comments.
- The compiler outputs are in `compile_*.txt`, and the step-by-step record is in `log.md`.

## 2. `HeckeFibreSizes`: proved from three leaves

### 2.1 The computation (VERIFIED, `fibre_sizes.py`, output `fibre_sizes.out`)

The computation works in the kernel's coordinates, with `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩ ⊂ (2, −3)`.

- `|𝒪/3𝒪| = 81` and `|(𝒪/3𝒪)^×| = 72`. The units of `𝒪/3𝒪` are exactly the residues with
  `nrd ≢ 0 mod 3`.
- **CM elements.** `𝒪` contains elements with `x² = −1`, with `x² − x + 1 = 0`, and with `x² = −6`.
  Their unit groups have orders 4, 6 and 2.
- **Units mod 3.** No unit of finite order other than `1` is `≡ 1 mod 3𝒪`:
  `nrd(g − 1) ∈ {1, 2, 3, 4}`, while every element of `3𝒪` has `9 ∣ nrd`.
- **Orbits.** Right multiplication by these unit groups on `(𝒪/3𝒪)^×` is free, with 18, 12 and 36
  orbits.
- **Atkin–Lehner fixed points.** Take an elliptic `μ ∈ 𝒪` of norm `m ∈ {2, 3, 6}` and trace `t`
  with `t² < 4m`. The field `ℚ(√(t² − 4m))` embeds in `B` only in two cases:
  - `(2, 2)` gives `ℚ(i)`;
  - `(3, 0)`, `(3, 3)` and `(6, 0)` give `ℚ(√−3)` and `ℚ(√−6)`.

  The fields `ℚ(√−2)`, `ℚ(√−7)`, `ℚ(√−11)`, `ℚ(√−5)`, `ℚ(√−15)` and `ℚ(√−23)` do not embed,
  because 2 or 3 splits in them.
- **Composition of the twists.** `tt_k · tt_l ∈ ℚ^× · tt_{k ⊕ l}`, so the twists form
  `W = (ℤ/2)²`.
- **Sizes.** The fibre has `r · 72 / a` classes, where `a = |Aut(A, ι)|` and
  `r = #(isomorphism classes among the 4 twisted pairs)`. This gives:
  - generic: `4 · 36 = 144`;
  - CM by `ℤ[i]`: `2 · 18 = 36`;
  - CM by `ℤ[ζ₃]`: `2 · 12 = 24`;
  - CM by `ℤ[√−6]`: `2 · 36 = 72`.

  In each case `144` divides `4·36`, `6·24` and `2·72`, as `HeckeFibreSizes` requires.

### 2.2 The leaves

All three are stated over the kernel's genuine abelian varieties `PkgI3.AbVar ℚ̄`. The definitions
`QMStr`, `QMIso`, `com`, `HasCM4`, `HasCM3` and `HasCM24` are the kernel's.

| Leaf | Statement | Source (locators UNVERIFIED) |
|---|---|---|
| `QMAutCard` | For an abelian surface with QM by `𝒪`: `Nat.card (QMIso q q)` is `4` under CM by `ℤ[i]`, `6` under CM by `ℤ[ζ₃]`, and `2` otherwise; and the three CM types are mutually exclusive. | Shimura's classification: `End⁰(A)` is `B` or `M₂(K)` with `K` imaginary quadratic, so `com(ι)` is `ℤ` or an order in `K` (Shimura 1963; Rotger, J. reine angew. Math. 561 (2003)); then units of quadratic orders. |
| `SerreRigidity3` | An endomorphism of finite order of an abelian variety over `ℚ̄` that fixes every `x` with `x³ = 1` is `1`. | Serre's lemma in finite-order form (Serre, Sém. Cartan 1960/61, exp. 17; Silverberg–Zarhin, JPAA 111 (1996)). Mumford §21 Thm 5 is the polarized form. |
| `ALFixedPoints` | `(A, ι ∘ t_m) ≅ (A, ι)` forces CM by `ℤ[i]` for `m = 1` (`w₂`), `ℤ[ζ₃]` for `m = 2` (`w₃`), and `ℤ[√−6]` for `m = 3` (`w₆`). | Fixed points of Atkin–Lehner involutions on `X₀⁶(1)` (Ogg 1983; Rotger, Trans. AMS 356 (2004)), together with §2.1's embedding check. |

Derivation of `ALFixedPoints`, checked independently by the reviewer:

- Let `φ : (A, ι∘Ad μ) ≅ (A, ι)`. Then `ψ = φ·ι(μ)` commutes with `ι(𝒪)`, and `ψ² = u·μ²` with
  `u = φ² ∈ com^×`.
- A rational `ψ` with `ψ² = ±2, ±3, ±6` is impossible. So `com ⊗ ℚ = K` is imaginary quadratic.
- `K = ℚ(√−2)` does not split `B`.
- For `μ = j`, the order contains `√−3`. It is maximal at 2 because `𝒪 ⊗ ℤ₂` is the maximal order
  of the 2-adic division algebra. So it contains `ζ₃`.

### 2.3 The proof (compiled, `FibreSizesMain.lean.part`)

- `lvEquiv`. The level structures on a fixed pair are in bijection with the 72 units of `𝒪/3𝒪`.
  The ingredients are `Level3.torsor` (from `TorsionStructure`), ts-hecke's table of units, and the
  reduced norm mod 3.
- `rep_rep : rep k (rep l a) = rep (k ⊕ l) a`. This uses `tt_mul` (16 quaternion products) and
  `conj_conj`.
- `range_Ψ`. The map `Ψ(k, c) = [(A, ι∘t_k, η_k·u_c)]` from `Fin 4 × (𝒪/3𝒪)^×` is onto
  `twistFibre P`.
- `push_injective` (where Serre's lemma enters). Distinct isomorphisms push a level structure to
  distinct level structures. Finite order comes from `Finite (QMIso q q)` by pigeonhole.
- `fibre_card`. Each fibre of `Ψ` is in bijection with `Σ l, QMIso(q_k, q_l)`, which has `s · a`
  elements. Here `s = #{m | (A, ι∘t_m) ≅ (A, ι)}`, and the count uses `k ⊕ ·`.
- `ncard_mul`: `#twistFibre · s · a = 288`.
- `heckeFibreSizes_of`. A case analysis with `M = 144`:
  - `s = 1` without CM;
  - `s ≤ 2` at CM points (`ALFixedPoints` plus exclusivity);
  - `a` from `QMAutCard`.

## 3. `HeckeNoVertRam`

**Compiled (`NoVertMain.lean.part`):**

- `ramIdx_eq_of_under_eq`. Let `E/F` be Galois with `F = Frac A`, where `A` is any integrally closed
  domain. Then two primes of `integralClosure A E` over the same prime of `A` have equal
  `Ideal.ramificationIdx`. The proof uses `IsGaloisGroup.of_isFractionRing`,
  `Algebra.IsInvariant.exists_smul_of_under_eq` and `Ideal.ramificationIdx_smul`. Mathlib's
  `ramificationIdx_eq_of_isGaloisGroup` needs a maximal prime; `p ℤ[X]` is not maximal.
- `isFractionRing_int`: `ℚ(X) = Frac ℤ[X]`.
- `noVerticalRam_of_witness : VertUnramWitness E p → NoVerticalRam E p`, for Galois `E`.
- `heckeNoVertRam_of_witness : HeckeVertWitness → HeckeNoVertRam`.

**Honest scope.** `HeckeVertWitness` asks for one prime over `p ℤ[X]` with `e = 1`, for each
`p > 324`. By lying over such a prime exists, so the witness form is **equivalent** to
`HeckeNoVertRam` (reviewer, VERIFIED by argument). The reduction changes the shape of the
statement ("one" instead of "all"). It does not change its content. What the witness needs is
arithmetic input. Two routes:

- **(GR) Good reduction.**
  - `Y₃` has a smooth proper model `𝒴/ℤ_(p)` for `p ∤ 6` (Morita 1981; Carayol 1986; UNVERIFIED).
  - The local ring of `𝒴` at the generic point `ξ` of a component of the special fibre is a DVR of
    `E` with uniformizer `p`, because the special fibre is reduced.
  - If `X` has nonconstant reduction on that component, then this valuation restricts to the Gauss
    valuation of `ℚ(X)`. Its centre on the integral closure is then a vertical prime with `e = 1`.
  - "Nonconstant reduction of `X`" is the arithmetic content: the tame quotient `𝒴/Γ'` is
    `P¹_{ℤ_(p)}` in the coordinate `j`. Here `X` must be the canonical coordinate. With `X = p·j`
    there would be vertical ramification.

    R2fp fixes `π`'s values `0, ∞, −16/27` at the three CM types, and `π` induces `Y/Γ' ≅ P¹`. So
    `π` is the canonical `j` up to a Möbius map fixing three points, which is the identity
    (SPECULATIVE, not formalized).
- **(NV) Lemma NV of h-b1 §3.** Tameness, unramified branch fibres (`residue_unramified_over_branch`,
  compiled in the kernel), Abhyankar at `(p, X − b)`, and the `W`-quotient. ts-hecke §6 explains
  why branch data alone cannot suffice.

**Suggested next decomposition (not done).** Split the witness into two pieces:

- a leaf: the smooth proper model of `Y₃` over `ℤ_(p)`;
- a glue Prop: a DVR `R ⊂ E` with uniformizer `p`, `ℤ[X] ⊆ R`, and `𝔪_R ∩ ℤ[X] = p ℤ[X]`.

The step from the DVR to `VertUnramWitness` is commutative algebra that can be proved:

- `B_Z` is Noetherian and normal (Mathlib: finite integral closure);
- the contraction of `𝔪_R` to `B_Z` has height 1;
- `(B_Z)_Q` is a DVR dominated by `R`, hence equal to `R`;
- so the length of `R/pR` is 1.

## 4. `CurveNormChart` and `CurveChartInf`

**Compiled (`CurveChartMain.lean.part`):**

- `ev_fromSpec`: the value of `s ∈ Γ(X, U)` at `Spec χ → Spec Γ(X, U) → X` is `χ s`. It uses
  image-plane's value calculus (`ev_comp`, `ev_spec_top`).
- `curveNormChart_of : ChartFinite → ChartNormal → CurveNormChart`:
  - take `E = Frac Γ(Y, π.U)`;
  - `Γ(Y, π.U) ≅ integralClosure ℚ[X] E` by `IsIntegralClosure.equiv`;
  - `[E : ℚ(X)] < ∞` by `IsIntegralClosure.isLocalization` and `Module.Finite.of_isLocalization`;
  - the chart is `Spec B ≅ Spec Γ(Y, U) → Y` through `IsAffineOpen.fromSpec`.
- `curveChartInf_of : ChartFiniteInf → ChartNormalD → InfFnField → CurveChartInf`. It is the same
  construction on `V = π⁻¹(P¹ ∖ {0})`, using the coordinate `s ↦ π.g`.
- `loc_max_dvr`. The localizations of `Γ(Y, U)` at maximal ideals are integrally closed domains:
  they are the local rings at closed points (`IsAffineOpen.isLocalization_stalk'`), which are DVRs
  (infra-smooth-dim's stalk dimensions, curve-glue's `isDomain_of_dim_one`, Mathlib's DVR TFAE).
  From this, **`chartNormalD`, `curveSectionsDomain` and `chartNormal` are theorems**.
- `finite_of_proper_qf`. A proper, locally quasi-finite `W → 𝔸¹` given by `s ∈ Γ(Y, W)` has `W`
  affine and `Γ(Y, W)` finite over `ℚ[X]`. The proof uses Mathlib's ZMT corollary
  `IsFinite.of_isProper_of_locallyQuasiFinite`, together with `isAffine_of_isAffineHom` and
  `IsFinite.SpecMap_iff`.
- From these: `chartFinite_of`, `chartFiniteInf_of`, `curveNormChart_of_charts` and
  `curveChartInf_of_charts`.

**Remaining glue** (curve theory, no moduli; true; proof sketches are in the docstrings):

| Prop | Content | Route |
|---|---|---|
| `ChartProper` | `π⁻¹(𝔸¹) → 𝔸¹` (by `π.f`) and `π⁻¹(P¹∖{0}) → 𝔸¹` (by `π.g`) are `IsProper` | valuative criterion (Mathlib `ValuativeCriterion`): a valuation-ring point with integral `π.f` cannot meet `π = ∞`, since `f g = 1` on `U ∩ V` |
| `ChartQuasiFinite` | both are `LocallyQuasiFinite` | closed fibres from the finite `ℚ̄`-fibres (ts-hecke's `exists_qbar_point`); the generic fibre consists of generic points of components |
| `ChartDominant` | for `Y ≠ ∅`, `π.U ≠ ∅`, and `ℚ[X] → Γ(Y,U)`, `ℚ[s] → Γ(Y,V)` are injective | a polynomial relation for `π.f` would make a `π`-fibre infinite |
| `InfFnField` | if `E` carries the chart over `𝔸¹`, then `E = Frac Γ(Y, V)` through a map with `π.g ↦ 1/X` | the chart's image is `U` (Jacobson); `Γ(Y,U) ≅ B`; `Γ(U∩V) = B[1/X] = Γ(V)[1/g]`; `g` is a nonzerodivisor (localizations of `Γ(V)` at maximal ideals are DVRs) |

**Self-review fix.** As first written, `ChartFiniteInf` and `ChartDominant` were **false** for
`Y = ∅`: all their hypotheses hold, but `Γ(Y, V) = 0`. Both now assume `Nonempty Y.left`, which
`curveChartInf_of` derives from `NormalizationModel`.

## 5. Independent review (read-only model agent, no Lean)

**Verdict on Part 1 and Part 2:**

- the three leaves are true as stated and are consequences of the cited results, not stronger;
- they are not vacuous and not disguised forms of the target;
- the count `n · s · a = 288` and the case analysis are correct.

**Findings:**

- the Serre citation was corrected (above);
- `HeckeVertWitness` is equivalent to `HeckeNoVertRam` (stated in §3);
- the canonical-coordinate caveat applies equally to the original target (§3).

Part 3 was written after the review and has not been reviewed independently.

## 6. What remains (for the announcement)

| Prop | Kind | Where |
|---|---|---|
| `QMAutCard`, `SerreRigidity3`, `ALFixedPoints` | **leaves** (new) | §2.2 |
| `Y3Connected`, `R1R2fp`, `ObjBridge.TorsionStructure` | leaves (existing) | ts-hecke |
| `ChartProper`, `ChartQuasiFinite`, `ChartDominant`, `InfFnField` | glue (curve theory) | §4 |
| `HeckeVertWitness` | glue from a leaf (good reduction of `Y₃`), equivalent to `HeckeNoVertRam` | §3 |
