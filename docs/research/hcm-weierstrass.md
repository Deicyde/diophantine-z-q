# hcm-weierstrass: the Weierstrass map is biholomorphic, and step G1 of `hCM` is proved

Task hcm-weierstrass, 2026-11-17. Base: origin/main 27657ffb. Log: `scratch/hcm-weierstrass/log.md`.
Lean: `ZInQKernel/Contrib/OneProof/ShimuraThm54Biholo.lean` (namespace `ZInQ.Contrib.HCMWeierstrass`, 60 KB,
imports only `ZInQKernel.Contrib.OneProof.ShimuraMainCM`). Development copy: `scratch/hcm-weierstrass/W.lean`,
assembled from `A_Charts.lean` and `B_body.lean` … `G_body.lean` by `assemble.sh`.

## 1. Result

Step G1 of the 11-16 review of `hCM` is now a Lean theorem. G1 is the gap between Shimura's "analytic isomorphism
`ξ : ℂ/𝔞 → E(ℂ)`" and the clause form `IsAnalyticUnif` that `ZInQ.Contrib.HCMDict.ShimuraThm54` uses. The proof
adds no hypotheses. Everything below is VERIFIED: it compiles, and `#print axioms` gives only `propext`,
`Classical.choice` and `Quot.sound` (`scratch/hcm-weierstrass/Axioms-output.txt`).

1. **The complex manifold `E(ℂ)`.** Take a short Weierstrass model over `ℂ` (`[E.IsElliptic] [E.IsShortNF]`).
   * Its points `E.toAffine.Point` get a topology (`pointTopology`) and an atlas (`chartedSpacePoint`).
   * Every chart is one of three coordinates (`atlas_coord`): `x`, `y` or `t = -x/y`.
   * The chart at `P` (`chartAt_coe`) is `t` at `O`, `y` at the points with `y = 0`, and `x` elsewhere.
   * The transition maps are analytic, so `IsManifold 𝓘(ℂ) ω E(ℂ)` holds (`isManifoldPoint`).
2. **The Weierstrass map is biholomorphic** (`toPoint_isAnalyticIso`). The map `ξ_L` sends `z ↦ (℘_L(z), ℘'_L(z)/2)`
   and lattice points to `O`. Then:
   * its fibres are the cosets of `L`, and it is onto;
   * it is a local biholomorphism `ℂ → E_L(ℂ)`, in the sense of Mathlib's `IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω`.

   So it induces a biholomorphism `ℂ/L ≅ E_L(ℂ)`. This covers items (2) and (3) of the task: holomorphic in the charts,
   bijective from `ℂ/Λ`, and with holomorphic inverse.
3. **The dictionary** (item (4)). Here `IsAnalyticIso W Λ ξ` means: the fibres of `ξ` are the `Λ`-cosets, `ξ` is
   onto, and `ξ` is a local biholomorphism. Then:
   ```
   isAnalyticUnif_iff_isAnalyticIso      : IsAnalyticUnif W Λ ξ ↔ IsAnalyticIso W Λ ξ ∧ ∀ z w, ξ (z + w) = ξ z + ξ w
   isAnalyticUnif_iff_isAnalyticIso_zero : IsAnalyticUnif W Λ ξ ↔ IsAnalyticIso W Λ ξ ∧ ξ 0 = 0
   ```
   The second rests on `add_of_isAnalyticIso`: a biholomorphism `ℂ/Λ → E(ℂ)` with `0 ↦ O` is a group homomorphism.
   So the dictionary holds in both readings of the print's "analytic isomorphism", with or without the group law.
4. **The new leaf and the discharge.**
   ```
   theorem ZInQ.Contrib.HCMWeierstrass.shimuraThm54_of_biholo (h : ShimuraThm54Biholo) :
       ZInQ.Contrib.HCMDict.ShimuraThm54
   ```
   `ShimuraThm54Biholo` is Shimura's theorem with "analytic isomorphism" meaning `IsAnalyticIso` (section 3).

`#discharges`: see section 5. In the fold, `hCM` is replaced by `ShimuraThm54Biholo`
(`scratch/hcm-weierstrass/FoldCheck.lean`, `autofold.json`). The fold is manual, since `hCM` is a top-level hypothesis.

With this, the rating of `hCM` depends only on two things: R2 (Shimura's §5.2 definition of `s⁻¹𝔞` through
localizations, against the Lean `sInvLat` defined through the closure in the finite adeles), and the reading of the
theorem number and wording.

## 2. The complex structure on `E(ℂ)` (VERIFIED)

**Topology.** `E.toAffine.Point` is the one-point compactification of the affine points
`AffPt W = {p : ℂ × ℂ // W.Nonsingular p.1 p.2}`, with `O` as the point at infinity. The homeomorphism is
`pointHomeo : E.toAffine.Point ≃ₜ OnePoint (AffPt W)`.
* For a smooth plane cubic this is the subspace topology of `ℙ²(ℂ)`. The reason (STANDARD, not formalized): `E(ℂ)` is
  compact Hausdorff, and its affine part is open, dense, and not compact.
* The definition is intrinsic. It is given for every `W : WeierstrassCurve ℂ`, and the uniformization plays no part in
  it.
* For elliptic `E` the space is compact Hausdorff (`compactSpacePoint`, and the `T2Space` instances): the affine
  curve is closed in `ℂ²`, hence locally compact.

**Coordinates.**
* `xC`, `yC`: the affine coordinates.
* `tC`: the coordinate `-x/y`, with `tC O = 0`.
* `coordFor P`: `tC` if `P = O`, `yC` if `y(P) = 0`, and `xC` otherwise.

**Charts.** A `ChartDatum ξ` is a pair `(c, e)`, where:
* `c : E(ℂ) → ℂ` is a coordinate;
* `e` is a partial homeomorphism of `ℂ` with nonzero complex derivative on its source;
* `c ∘ ξ = e` on the source of `e`.

Its chart is `c` on the open set `ξ(source e)`, with inverse `ξ ∘ e⁻¹` (`ChartDatum.chart`). The atlas consists of
the charts of the data whose coordinate is `xC`, `yC` or `tC`. `chartAt P` is a chart with coordinate `coordFor P`.

The uniformization `ξ` (a chosen `unif W`) is used only to *prove* that these intrinsic coordinates are local
coordinates and that they are compatible:
* `exists_chartDatum` is the inverse function theorem;
* `transition_contDiffOn`: a transition map is locally `e₂ ∘ (· - l) ∘ e₁⁻¹`, hence holomorphic, hence `C^ω` by
  `DifferentiableOn.contDiffOn`.

The atlas is determined by the topology and the three coordinate functions. Every chart's function is `x`, `y` or
`-x/y` (`atlas_coord`).

**Local coordinates along `ξ_L`** (B_body):

| point | coordinate | `c ∘ ξ_L` near a preimage `z₀` | derivative at `z₀` |
|---|---|---|---|
| `O` | `t = -x/y` | `2(z + z³E(z))/(2 - z³D(z))`, where `E = ℘[L - 0]` and `D = ℘'[L - 0]` | `1` |
| `y = 0` | `y` | `℘'/2` | `℘''(z₀)/2 = 3x₀² - g₂/4 ≠ 0` |
| otherwise | `x` | `℘` | `℘'(z₀) = 2y₀ ≠ 0` |

* At `O` the formula comes from `℘ = E + 1/z²` and `℘' = D - 2/z³`. These are Mathlib's `weierstrassPExcept_add` and
  `derivWeierstrassPExcept_sub`; `E` and `D` are analytic at `0`.
* At the points with `y = 0`, `℘'' = 6℘² - g₂/2` holds off `Λ` (`deriv_derivWeierstrassP`). The derivative of the
  differential equation gives `℘' · (2℘'' - 12℘² + g₂) = 0`. The zeros of `℘'` are isolated: otherwise, by the
  identity theorem on the connected set `ℂ ∖ Λ` (the complement of a countable set), `℘' ≡ 0`, which contradicts
  `℘'(ω₁/4) ≠ 0`.
* Nonsingularity of `(x₀, 0)` gives `3x₀² + a₄ ≠ 0`.

**Continuity and openness of `ξ_L`** (`continuous_toPoint`, `isOpenMap_toPoint`):
* At lattice points, continuity follows from `‖℘‖ → ∞` (`eventually_large_weierstrassP`), using the basis of
  neighbourhoods of `∞` in `OnePoint`.
* Openness: a compact set `K` meets every coset (`exists_compact_fund`). Then
  `ξ(U)ᶜ = ξ(K ∖ (U + Λ))` is compact, hence closed.

**Abstract part** (A_Charts). Suppose `ξ` is continuous and open, its fibres are the `Λ`-cosets, and chart data cover
`E`. Then:
* the atlas is analytic (`isManifoldOf`);
* `ξ` is `C^ω` (`contMDiff_of`);
* `ξ` is a local diffeomorphism (`isLocalDiffeomorph_of`): the local inverse at `z` is `Q ↦ e⁻¹(c Q) + l`.

## 3. The new leaf

```lean
def ShimuraThm54Biholo : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic] [E.IsShortNF],
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticIso E (kappa m '' 𝔞) ξ → ξ 0 = 0 →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticIso (E.map (σ : ℂ →+* ℂ)) (kappa m '' sInvLat m s 𝔞) ξ' ∧
      ∀ u v : QNeg m,
        finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
        conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)

def IsAnalyticIso (W : WeierstrassCurve ℂ) [W.IsElliptic] [W.IsShortNF] (Λ : Set ℂ)
    (ξ : ℂ → W.toAffine.Point) : Prop :=
  (∀ z w, ξ z = ξ w ↔ z - w ∈ Λ) ∧ Function.Surjective ξ ∧ IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ξ
```

Everything except `IsAnalyticIso` is copied unchanged from `ShimuraThm54`: `QNeg`, `ιC`, `kappa`, `ArtinCond`,
`sInvLat`, `finPart`, `latHat`, `AfK`, `conjPt`.
* `E.IsShortNF` is Mathlib's class for `a₁ = a₂ = a₃ = 0`.
* `IsLocalDiffeomorph` is Mathlib's.
* The manifold structure is that of section 2. `isShortNF_map` supplies the instance for `E^σ = E.map σ`.

**Rating: printed form, read up to R2. Kind published, flag pending reading (R2); locator UNVERIFIED.** The reasons:

* *Hypothesis.* The leaf takes `ξ` an analytic isomorphism with `ξ(0) = O`. If the print means a group
  isomorphism, such a `ξ` qualifies (`isAnalyticUnif_iff_isAnalyticIso_zero`). If the print means a biholomorphism,
  the leaf restricts the print to `ξ(0) = O`. Either way the leaf's hypothesis is a special case of the print's.
* *Conclusion.* The leaf asks only that `ξ'` be an analytic isomorphism, with no group law. That follows from the
  print in either reading.
* *Other differences*, each weaker than or equal to the print: the uniqueness of `ξ'` is dropped; `E` ranges over short
  Weierstrass models only (every elliptic curve over `ℂ` has one); `𝔞` comes with a period pair.
* *Not settled here.*
  * R2: the Lean `s⁻¹𝔞 = sInvLat m s 𝔞 = K ∩ s_f⁻¹ closure(𝔞)` and `s⁻¹u` (through `latHat`), against Shimura's
    §5.2 definitions through `p`-components. Task hcm-lattice (origin/wip/hcm-lattice) proved
    `(sInvLat s 𝔞)_p = s_p⁻¹𝔞_p` and the local–global principle in its scratch file. Once that file is in the tree,
    a leaf combining its `s⁻¹𝔞` with this file's `IsAnalyticIso` is a short glue file.
  * The theorem numbers: Shimura 1971 Thm 5.4 and Lang, *Elliptic functions*, Ch. 10 Thm 3 are UNVERIFIED (from
    memory; no copy on the host).
* *Genuine definitions.* `IsAnalyticIso` is stated over Mathlib's manifold API with an intrinsic atlas. It is
  satisfiable (`toPoint_isAnalyticIso`), and it is not a disguised form of the conclusion: it constrains only `ξ`.

Why `ShimuraThm54Biholo → ShimuraThm54` holds (`shimuraThm54_of_biholo`):
* *Hypothesis.* `IsAnalyticUnif ξ` gives `IsAnalyticIso ξ ∧ ξ 0 = O`.
* *Conclusion.* `ξ'(0) = ξ(0)^σ = O`. Take `u = v = 0`, which is admissible because `0 ∈ 𝔞`, from `κ` injective and
  `0 ∈ L.lattice`. Then `IsAnalyticIso ξ' ∧ ξ'(0) = O` gives `IsAnalyticUnif ξ'`.

## 4. Lean inventory (`ZInQ.Contrib.HCMWeierstrass`, all VERIFIED)

| part | declarations |
|---|---|
| A, abstract charts | `ChartDatum`, `ChartDatum.chart`, `ChartDatum.local_form`, `ChartDatum.contDiffAt_comp`, `chartedSpaceOf`, `transition_contDiffOn`, `isManifoldOf`, `contMDiff_of`, `isLocalDiffeomorph_of`, `exists_chartDatum` |
| B, topology | `AffPt`, `toOnePoint`, `pointEquiv`, `pointTopology` (scoped instance), `pointHomeo`, `xC`, `yC`, `tC`, `coordFor` |
| C, Weierstrass map | `toPoint_eq_iff`, `eventually_large_weierstrassP`, `isClosed_nonsingular`, `continuous_toPoint`, `exists_compact_fund`, `isOpenMap_toPoint`, `isPreconnected_compl_lattice`, `deriv_derivWeierstrassP`, `exists_chartDatum_zero`, `exists_chartDatum_some`, `exists_chartDatum_toPoint` |
| D, manifold | `UnifProps`, `unifProps_toPoint`, `exists_unifProps`, `unif`, `chartedSpacePoint`, `atlas_coord`, `chartAt_coe`, `isManifoldPoint`, `unif_isLocalDiffeomorph`, `IsAnalyticIso` |
| E, dictionary with the group law | `isLocalDiffeomorph_comp_mul`, `exists_eq_unif_mul`, `isAnalyticIso_of_isAnalyticUnif`, `exists_local_lift_unif`, `isAnalyticUnif_of_isAnalyticIso`, `isAnalyticUnif_iff_isAnalyticIso`, `toPoint_isAnalyticIso` |
| F, Shimura's reading | `compactSpacePoint`, `deriv_eq_of_lifts`, `eq_unif_mul_of_isAnalyticIso`, `add_of_isAnalyticIso`, `isAnalyticUnif_iff_isAnalyticIso_zero` |
| G, leaf | `isShortNF_map`, `ShimuraThm54Biholo`, `shimuraThm54_of_biholo` |

`eq_unif_mul_of_isAnalyticIso` proves that a biholomorphism with `0 ↦ O` is `z ↦ unif(αz)`, in five steps:
1. A compact `K` meets every fibre of `ξ`: `E(ℂ)` is compact and `ξ` is open.
2. `ξ` has holomorphic local lifts `G` through `unif`, from the local inverses of `unif`.
3. Two lifts differ locally by a constant lattice element, because the lattice is discrete. So `φ(z) = G_z'(z)` is a
   well-defined entire function.
4. `φ` is constant on the fibres of `ξ`, hence bounded by its maximum on `K`, hence constant by Liouville.
5. `{z | ξ z = unif(αz)}` is clopen and contains `0`, so it is all of `ℂ`.

## 5. Checks

* `lake build ZInQKernel.Contrib.OneProof.ShimuraThm54Biholo`: Build completed successfully, 37 s for the file.
* Axioms: `scratch/hcm-weierstrass/Axioms-output.txt`.
* `#discharges`: `scratch/hcm-weierstrass/Discharges-output.txt` (see the log for the outcome).
* Fold: `scratch/hcm-weierstrass/FoldCheck.lean` (output `FoldCheck-output.txt`).
* The file has no `sorry`, no `axiom`, and no `#eval`, `run_cmd`, `initialize`, `syntax`, `notation` or macros.
  All instances are `scoped`, except the Prop instance `isShortNF_map`.

## 6. kinds.tsv proposal for the `hCM` row

* Kind: `consequence` → `published`.
* Strict: GLUE → LEAF. G1 is proved, and the leaf is weaker than or equal to the print in both readings.
* Strictest: GLUE stays until R2 is proved in the tree or read away.
* Flag: "pending reading: R2 (s⁻¹𝔞 through the closure in 𝔸_K,f vs Shimura §5.2's p-components; hcm-lattice proved
  the equality in scratch); G1 proved in Lean by hcm-weierstrass (isAnalyticUnif_iff_isAnalyticIso_zero); locator
  UNVERIFIED (numbers)".
* Count: strict GLUE −1, strictest unchanged.

## 7. Relation to the other hCM tasks

* **hcm-g1** (`f4f7d8db`): `IsAnalyticIso` there is again a clause form (a surjective group homomorphism with
  holomorphic coordinates off the lattice).
* **hcm-lattice**: `IsAnalyticIso` is a holomorphic map into `ℙ²` with nowhere-vanishing differential, inducing a
  bijection. Its docstring says this is a biholomorphism, but no manifold structure is built.
* **This file** builds the complex manifold `E(ℂ)` with Mathlib's `ChartedSpace` and `IsManifold`, and proves that the
  Weierstrass map is a local biholomorphism (Mathlib's `IsLocalDiffeomorph`) with the right fibres. That is the
  printed notion itself.
