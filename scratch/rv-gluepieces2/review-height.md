# rv-gluepieces2: adversarial review of the height fields of `GluePieces2`

Read-only model review, 2026-11-13; no Lean run. `G0Assemble.lean`, `GluePieces2` L41938-41998.

Marks: VERIFIED = read/diffed; STANDARD = published; SPECULATIVE = estimate; locators UNVERIFIED.

## Summary

| Field | Def (line) | Verdict | Wave-27 status (transfer) |
|---|---|---|---|
| `analyticUniformizationUnique` | `ZInQ.DefFaltings.AnalyticUniformizationUnique` (L18100) | **TRUE** | not attacked by wave 27 |
| `metrizationDimUnique` | `ZInQ.G0HeightAdd.MetrizationDimUnique` (L37049) | **TRUE** (proved) | proved by metrization over byte-identical defs |
| `metrizationExists` | `ZInQ.G0HeightAdd.MetrizationExists` (L37041) | **TRUE** | reduced by metrization (identical defs); needs a LEAF |
| `productMetrizationGeo` | `ZInQ.G0HeightAdd.ProductMetrizationGeo` (L37153) | **TRUE** | reduced by metrization (identical defs) |
| `hodgeLineBaseChange` | `G0StableBC.HodgeLineBaseChange` (L36852) | **TRUE** | reduced by height-bc; same text, but stated over the kernel's `PkgI3.AbVar`, so it does not transfer literally |

No false, vacuous or inert field among these five; two classification problems, transfer caveats.

## 0. Common dependencies (VERIFIED by reading/diff)

- Namespace resolution. L18100 is in `namespace ZInQ.DefFaltings` (L16746-18648). L20192 is in
  `namespace ZInQ.LeafPush2` (L18862-21119, with `open PkgI3`), so it is the separate constant
  `ZInQ.LeafPush2.AnalyticUniformizationUnique` over LeafPush2's `GroupModel`. The two bodies are
  textually identical. GluePieces2 L41951 writes the fully qualified `ZInQ.DefFaltings.…`. No
  `HSyn.ZInQ…` or `G0Split.ZInQ…` namespace exists (grep), so the field is the **L18100** copy.
  `productModelHeight_of` (L37067, `open DefFaltings` inside `ZInQ.G0HeightAdd`) uses the same one.
- The objects are concrete, not opaque. `GroupModel` (L17878) is a smooth, separated,
  quasi-compact group object over `Spec 𝓞_L` with a group iso `genericFibre ≅ A_L`.
  `Pts τ = (ptC τ ⟶ 𝒢.G)` (L18043) has Mathlib's group law. `evalAt` (L18049) evaluates a section
  at a ℂ-point through `appLE` and `ΓSpecIso`. `dom` (L18057) is `Φ⁻¹(U(ℂ))`.
  `IsAnalyticUniformization` (L18060) says: homomorphism, kernel exactly `Λ`, surjective, every
  `dom Φ U` open, and every regular function holomorphic along `Φ` on `dom Φ U`. `hodgeSpace`,
  `detLattice`, `omega`, `wedge` (L17996-18013), `germAlong` and `jacDet` (L18069-18082),
  `HodgeData` (L17080), `MetrizedModel` (L18125), `secIndex` (L16783, `relIndex` of `𝓞s` in `M`)
  and `torusMetricSq = ‖c‖²·covol` (L17096) are all definitions over Mathlib.
- `IsAnalyticUniformization` pins holomorphy correctly (STANDARD argument). `𝒢` is smooth, hence
  locally of finite presentation. Take an affine open `V = Spec R ∋ Φ(z₀)` and generators `r_i`
  of `R` over `𝓞_L`. Then `p ↦ (r_i(p))` is a closed embedding of `V_τ(ℂ)` into `ℂ^N` for the
  analytic topology, and `r_i ∘ Φ` is holomorphic on the open set `dom Φ V`. So `Φ` is continuous
  and holomorphic for the analytic topology of `A_τ(ℂ)`. The clause does not only control the
  Zariski topology.

## 1. `AnalyticUniformizationUnique` (L18100): TRUE

**Statement.** For all `K, A, L, 𝒢, τ, g, Λ, Λ', Φ, Φ'`: if `Φ` and `Φ'` are analytic
uniformizations `ℂ^g → 𝒢(ℂ)_τ` with kernels `Λ` and `Λ'`, then there is
`T : ℂ^g ≃ₗ[ℂ] ℂ^g` with `Φ' = Φ ∘ T` and `z ∈ Λ' ↔ T z ∈ Λ`.

**Attack.** `Λ` and `Λ'` are *not* required to be discrete or full, and `g` is arbitrary (not
pinned to `d = dim A`). So I tested `g ≠ d` and non-discrete kernels.

**Argument (STANDARD).** By §0, `Φ` and `Φ'` are holomorphic surjective homomorphisms
`ℂ^g → A_τ(ℂ) ≅ ℂ^d/Λ₀`. Such a map lifts through the universal cover (`ℂ^g` is simply
connected) to a continuous additive map `M : ℂ^g → ℂ^d`. That map is ℝ-linear, and ℂ-linear by
holomorphy. Likewise `Φ'` lifts to `M'`.
- Surjectivity of `Φ` forces `M` onto. Otherwise `M(ℂ^g) + Λ₀` is a countable union of
  translates of a proper subspace, so it has measure zero.
- **`g < d`:** no uniformization exists, so the statement is vacuously true.
- **`g ≥ d`:** `M` and `M'` are surjective with kernels of the same dimension `g − d`. So there
  is `T ∈ GL_g(ℂ)` with `M ∘ T = M'` (choose bases adapted to the kernels). Then
  `Φ ∘ T = π ∘ M' = Φ'`, and `Λ' = ker Φ' = T⁻¹Λ`. This covers non-discrete kernels.
- **`d = 0`:** `Φ = Φ' = 1`, `Λ = Λ' = ⊤`, `T = id`.

The conclusion asks for exactly this. There is no hidden `Aut(A)` or `GL(Λ)` ambiguity, because
`T` acts on the source and `Φ` itself is compared.

**Classification problem (not a falsity).** The field is labelled GLUE. Proving it needs the
complex-Lie-group structure of `A_τ(ℂ)`: a torus quotient and covering-space lifting. That is the
same Mathlib gap as AN3 existence.
- bp-analytic's `IsUniformization.exists_equiv`
  (`ZInQKernel/HDecomp/Analytic/Uniformization.lean:333`, VERIFIED read) assumes both lattices
  are `DiscreteTopology`.
- The Prop here allows non-discrete kernels when `g > dim A`, so the adaptation also has to
  handle that case.
- Recommendation: add `[DiscreteTopology Λ] [DiscreteTopology Λ']` (and `IsZLattice`)
  hypotheses. The only consumer, `MetrizedModel.modelHeight_eq_of_model_eq` (L18295), applies the
  field to `hodge.periods`, which carry both instances (`periods_discrete`,
  `periods_isZLattice`). So the change costs nothing downstream and makes the Prop closer to the
  existing kernel lemma.
- With discreteness and `AnalyticUniformizationOfDim` it is still not elementary: `Φ` has to be
  shown to be a covering map, which needs compactness and Hausdorffness of `A_τ(ℂ)` (a
  GAGA-type input). It should be booked as LEAF-sized analytic input, or derived from bp-analytic.

## 2. `MetrizationDimUnique` (L37049): TRUE, and already proved

**Statement.** If `M : MetrizedModel A L g`, `M' : MetrizedModel A L g'` and
`M.model = M'.model`, then `g = g'`.

**Argument.** There are two cases.
- **`g, g' ≥ 1`:** `finrank_L (L ⊗ ⋀^g C) = 1` holds for at most one `g ≥ 1`. Here
  `C = 𝔪_ξ/𝔪_ξ²` has dimension `d`, and `⋀^g` has dimension `binom(d, g)`.
- **`g = 0 < g'`:** `Φ : ℂ⁰ → 𝒢(ℂ)_τ` is onto, so `Pts τ` is a singleton. But the discrete
  kernel of `Φ'` on `ℂ^{g'}` is not everything, so some `Φ' z ≠ 1`.

`d = 0` is fine: for `g ≥ 1` the Hodge space is `0`, so no metrization exists.

**Wave 27 (VERIFIED by diff).**
- `scratch/metrization/part_dim.lean:44` proves
  `theorem metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique` with no hypotheses. It
  uses `ExtLine.lean`'s `eq_of_finrank_one`.
- `Base.lean` is byte-identical to `scratch/g0-heightadd/HeightAdd.lean` (`cmp`). Its
  DefFaltings section (L35-1937) is identical to G0Assemble L16746-18648 (`diff` empty). Its
  H5Neron definitions (L1950-2190) match G0Assemble L29580-29815 up to blank lines. Its two
  G0HeightAdd blocks equal G0Assemble L37011-37083 and L37091-37175 (`diff` empty).
- So the proof is over the same text. Compilation is claimed by the task (0 errors, standard
  axioms); I did not re-run it.
- **Recommendation:** replace the field with the theorem. When appending
  `part_g0dim.lean`, drop it: it copies `G0Dim.dim_finite`, which G0Assemble already has
  (L35052/L35229), so it would clash.

Lean check (append after G0Assemble + `ExtLine.lean`'s lemma + `part_dim.lean`):
```lean
example : ZInQ.G0HeightAdd.MetrizationDimUnique := ZInQ.Metrization.metrizationDimUnique
```

## 3. `MetrizationExists` (L37041): TRUE (STANDARD), but not pure GLUE

**Statement.** Every `𝒢 : GroupModel A L` has some `g` and `M : MetrizedModel A L g` with
`M.model = 𝒢`.

**Attack.**
- **(a) Zero-dimensional `A`.** `g = 0`: `hodgeSpace 0 = L`, lattice `𝓞·(1⊗1)` with
  `secIndex = 1`, periods `⊤ = ⊥` in `ℂ⁰` (discrete and full), and `Φ ≡ 1`. Surjectivity holds
  because `Pts τ` is a point: the generic fibre is `Spec L`, and a ℂ-point over the generic point
  of `Spec 𝓞_L` is a point of `Spec L ⊗_τ ℂ`. `coeff(1⊗1) = jacDet Φ (empty) = det(0×0) = 1`.
  OK.
- **(b) Non-Néron, non-semistable models.** `detLattice d = ⋀^d ω_𝒢` is a full lattice for any
  smooth separated quasi-compact model (`HodgeLatticeTheorem`; `omegaAt` is the image of
  `I_{e(s)}/I²`, free of rank `d` over the DVR, inside `𝔪_ξ/𝔪_ξ² = (I/I²)⊗L`). Smoothness is
  part of `GroupModel`, so non-smooth models are excluded by the type.
- **(c) Coherence of `arch`.** It requires `coeff τ (wedge f) = jacDet Φ f` for *all* germ tuples.
  This is consistent because `jacDet Φ` is a τ-semilinear alternating function of the `df_i`.
  Metrization proved this as `jacDetDescends` (claimed VERIFIED). It is nonzero because `dΦ(0)`
  is invertible (`JacDetNondegenerate`).

**Wave 27 (VERIFIED read).** The proof is over identical defs (§2).
`metrizationExists_of' (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
(hN : JacDetNondegenerate)`. The new Props (`scratch/metrization/part_exists.lean:24,52`):
- `AnalyticUniformizationOfDim` (for `g = dim A`, a discrete full `Λ` and an analytic
  uniformization): TRUE, the uniformization theorem `A_τ(ℂ) ≅ ℂ^g/Λ` (Mumford §1, UNVERIFIED
  locator, plus GAGA). It is a LEAF, and the task labels it so.
- `JacDetNondegenerate` (some `f` with `jacDet Φ f ≠ 0` for `g = dim A`, discrete full kernel):
  TRUE. `Φ` is a local biholomorphism at `0` (the lift `M` is a linear iso since
  `ker = Λ` is discrete), and a regular system of parameters at `ξ` gives holomorphic
  coordinates on the smooth `A_τ`. It is glue, but it needs the complex-manifold structure.

**Classification problem.** GluePieces2 calls `metrizationExists` "GLUE", but its reduction
contains the uniformization theorem, a LEAF the project cannot prove from Mathlib v4.35.
`AnalyticUniformizationExists` (L18090) is in neither `ResearchLeaves` (L32975) nor
`TextbookLeaves` (L33027) (grep). The field should be booked as "glue + leaf AN3", or
`AnalyticUniformizationOfDim` added to a leaf bundle.

## 4. `ProductMetrizationGeo` (L37153): TRUE (STANDARD)

**Statement.** Suppose `IsProductModel eC 𝒢P 𝒢₁ 𝒢₂` and `Mᵢ` are metrizations of `𝒢ᵢ` (any
`gᵢ`). Then there are `MP : MetrizedModel C L (g₁+g₂)` with model `𝒢P`, and nonzero
`s, s₁, s₂` in the three lattices, such that:
- `secIndex` multiplies;
- `coeff σ` multiplies, with equality in `ℂ`, not only in absolute value;
- `covolume (periods σ)` multiplies.

**Attack.**
- **`IsProductModel` (L29750, VERIFIED).** It pins `𝒢P`: there is an iso `e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G`
  over `𝓞_L` whose projections are homomorphisms, compatible with the generic identifications.
  It is not just "same generic fibre", so the Néron-vs-arbitrary-model trap does not apply.
- **Multiplicative index.** `⋀^{top} ω_P ≅ ⋀ω₁ ⊗ ⋀ω₂` (`ω_P = p₁*ω₁ ⊕ p₂*ω₂` for a product of
  smooth group schemes). If `𝓞sᵢ = 𝔞ᵢΛᵢ`, then `𝓞(s₁⊗s₂) = 𝔞₁𝔞₂(Λ₁⊗Λ₂)` and `N(𝔞₁𝔞₂)`
  multiplies.
- **One factor of dimension 0.** `Λ₁ = 𝓞`, `s₁ = a·1`, `secIndex = |N(a)|`, and
  `s = a·s₂`. `covol` of the trivial lattice in `ℂ⁰` is 1 (Dirac volume), and the empty `jacDet`
  is 1. All three identities hold.
- **Coefficient equality in ℂ.** It holds only for `MP` built from `prodPts` (another
  uniformization changes `c` by `det T` with `|det T| = 1`), but the Prop is existential in `MP`,
  so this is fine. Metrization makes the same observation.
- `gᵢ` is not constrained in the statement. By §2 every metrization has `gᵢ = dim`, so nothing
  is lost.

**Wave 27 (VERIFIED read, identical defs).**
`productMetrizationGeo_of_local (hLS : ProductLocalStructure) (hPL : ProductHodgeLattice)`.
- `ProductLocalStructure` (`part_produnif2.lean:25`): TRUE. Take affine `Vᵢ = Spec Rᵢ`; then
  `V₁×V₂ = Spec(R₁⊗R₂)`. A basic open `D(h)` inside `e(U)` contains the point, `s = a/h^m` on it,
  and `H = h^m` and `a` are expanded as sums of pure tensors (pad to a common `n`).
- `ProductHodgeLattice` (`part_prodsplit.lean:46`): TRUE as stated. It asks for line-ness of
  `hodgeSpace (g₁+g₂)` (true since `g₁+g₂ = dim C`, forced by the existence of `Mᵢ`), pulled-back
  germ tuples in `castAdd`/`natAdd` order (sign `+1`), denominators `aᵢ` to land in the
  lattices, and multiplicative index. It is pure algebra (stalks of fibre products), and it is
  GLUE.

## 5. `HodgeLineBaseChange` (L36852): TRUE (STANDARD)

**Statement.** For `IsBaseChangeOf 𝒢' 𝒢` and every `g`, there is an additive
`ψ : hodgeSpace_𝒢 g → hodgeSpace_𝒢' g` that:
- (i) is `L`-semilinear;
- (ii) is injective on nonzero vectors;
- (iii) sends "line" to "line";
- (iv) gives exactly `detLattice' = span_{𝓞_{L'}} ψ(detLattice)`;
- (v) has a uniformization clause: every analytic uniformization `Φ` of `𝒢(ℂ)_{τ'|_L}` gives
  `Φ'` of `𝒢'(ℂ)_{τ'}` with the same `Λ`. Moreover, every `c'` with `c'∘ψ = c`, where `c`
  computes `jacDet Φ` on wedges, computes `jacDet Φ'` on wedges.

**Attack on the brief's main suspect (iso vs injection with finite cokernel).**
`IsBaseChangeOf` (G0StableBC copy, L36467; identical body to the H5Neron copy, L30153; VERIFIED)
requires a *group iso* `𝒢'.G ≅ 𝒢.G ×_{𝓞_L} 𝓞_{L'}`. So `𝒢'` is the honest base change, not some
model of `A_{L'}` (for example the Néron model over `L'`, which differs for non-semistable `A`).
For the honest base change, the formation of the conormal `e*(I/I²)` commutes with base change
(regular section of a smooth separated group scheme; EGA IV 16.4.5/17.2.5, UNVERIFIED). So
`ω_{𝒢'} = ω_𝒢 ⊗ 𝓞_{L'}`, and (iv) is an equality. The Prop does not claim invariance of the
Néron lattice.

**Other attacks.**
- **(a) All `g`, including `g > d`.** Both Hodge spaces are `0` and `ψ = 0`. In (v), `c` forces
  `jacDet Φ f = 0`, which holds: the rows `d(f_i∘Φ)(0)` lie in a ≤ d-dimensional space. `Φ'`
  exists for non-discrete `Λ`: `Φ' = β⁻¹∘Φ`, where `β` is a group bijection (proved by
  height-bc), and `Φ` is continuous for the analytic topology by §0. So preimages of Zariski
  opens of `𝒢'` are open, and sections of `𝒢'` are locally `(∑ fᵢ⊗aᵢ)/h`, hence holomorphic.
- **(b) The conclusion is for all germs `f'` of `𝒢'`, not only pulled-back ones.** Both sides are
  `𝓞_{L'}`-multilinear, τ'-semilinear and alternating in `df'_i`. The pulled-back differentials
  span `𝔪'/𝔪'²` over `𝓞_{L'}`, because `𝓞_{L'}·L = L'`. OK.
- **(c) Twist and embedding.** `τ'.comp (algebraMap L L')` agrees with
  `𝓞_L → 𝓞_{L'} → L' → ℂ`, because the `𝓞` algebra map is the restriction. OK.

**Wave 27 (VERIFIED read and diff).**
- Height-bc proves `hodgeLineBaseChange_of_glue4` from `HodgeBCInjective`, `CotangentSpanBC`,
  `OmegaBaseChange` and `UniformizationLiftAnalytic` (`scratch/height-bc/Final.lean`
  L1459/1752/1159/1853). All four are TRUE by the arguments above:
  - `binom(d, g)` on both sides, so the iff holds;
  - `𝓞_{L'}·L = L'`;
  - conormal base change gives `ω' ≤ span π*ω`;
  - holomorphy along `Φ'` follows from (a).
- `HodgeLineBaseChange` and `MetrizationBaseChange` are textually identical to G0Assemble's.
  `IsBaseChangeOf` differs only in binder placement.
- **Transfer caveat.** `Final.lean` imports `ZInQKernel.HDecomp.Faltings.Leaves`, where `AbVar`
  is `PkgI3.AbVar` (`Objects.lean:162`, `Type u`). G0Assemble's statement is over its own
  structure copy `ZInQ.DefFaltings.AbVar` (L17845, `Type`).
  - Kernel `Models.lean` L25-239 equals G0Assemble L17868-18084 up to whitespace (`diff -w`
    empty).
  - The two `AbVar`s have the same four fields, but they are different constants. So the
    height-bc proof does **not** literally discharge the G0Assemble field; it needs a
    re-elaboration over the copy.
  - Height-bc's `G0WithBC.lean` went the other way, aliasing
    `ZInQ.DefFaltings.AbVar := PkgI3.AbVar`.
  - SPECULATIVE: the port is mechanical, since `AbVar` enters only through `GroupModel.gen` and
    `AbVar.baseChange`, neither used by the Hodge-line proof.

## 6. Recommendations

1. Discharge `metrizationDimUnique` by the theorem (§2). 2. Add discreteness hypotheses to
`analyticUniformizationUnique` and book it as analytic LEAF-sized input. 3. Book
`metrizationExists` as glue plus the AN3 leaf. 4. Port height-bc onto G0Assemble's `AbVar` copy.
