# bp-faltings: formalization blueprint for the stable Faltings height

Status: research note and blueprint (task bp-faltings, 2026-11-12), written for a crowdsourced
Lean team. Lean drafts, all compiled and sorry-free: `scratch/bp-faltings/Hodge.lean` and
`scratch/bp-faltings/Models.lean`. Results log: `scratch/bp-faltings/log.md`. No file under
`ZInQKernel/` or `blueprint/`, and no other task's notes or scratch files, was edited.

Marks: **VERIFIED** means read in a source in the repository or in Mathlib, computed, or compiled.
**STANDARD** means a published result with a reference. **SPECULATIVE** means an estimate or a
proposal. **UNVERIFIED** marks a locator recalled from memory; there was no network access.
"BUILT" marks a node compiled in `scratch/bp-faltings/`.

## 0. Main result

1. **The definition splits into three independent strands. The only one that needs Néron models
   is not part of the definition.** (§1, §2)
   - The **Arakelov strand** (Hermitian lines on `Spec 𝓞_K`, the Arakelov degree) needs only
     Mathlib's number-field library.
   - The **archimedean strand** needs the period lattice of `A_σ(ℂ)`. The analytic
     uniformization `A(ℂ) ≅ ℂ^g/Λ` (node AN3) is the single largest missing piece.
   - The **model strand** needs a smooth group model `𝒢/𝓞_L` and its lattice
     `ω_𝒢 = e*Ω¹_{𝒢/𝓞_L}`.

   Define `h_F^st(A)` as the infimum of the model height over all finite `L/K` and all smooth
   separated finite-type group models `𝒢` of `A_L` (pkg-I5 §2.1; nodes M1, H3). Then Néron models
   (Néron, BLR) and Grothendieck's semistable reduction theorem enter only in the theorem "the
   infimum is finite and is attained by the Néron model over a semistable field" (node H5).
   The leaves R18-R22 can be **stated** without H5. H5 is needed only so that the definition
   provably means the published one, and the acceptance tests AT1/AT2 check that in the two cases
   that have closed formulas.
2. **The first concrete layer is built (VERIFIED: compiled; axioms `propext`, `Classical.choice`,
   `Quot.sound`; no `sorry`).** `Hodge.lean`, about 1 000 lines, Mathlib only:
   - `HermitianLattice`, the Arakelov degree `arakelovDegree`, and its independence of the
     section, `degreeAt_eq_arakelovDegree`. The proof uses the product formula and the index
     identity `secIndex_smul`: `#(M/𝓞·as) = |N(a)|·#(M/𝓞·s)`.
   - Part of node AR3:
     - for fractional ideals, the index formula `#(I/𝓞x)·N(I) = |N(x)|`
       (`secIndex_mul_absNorm`) and the closed formula
       `deg(I, ρ·|σ(·)|) = −log N(I) − ∑ log ρ_σ` (`arakelovDegree_ofFractionalIdeal`);
     - rescaling of the metrics (`arakelovDegree_rescale`);
     - base change: each embedding of `K` has exactly `[L:K]` extensions to `L`
       (`sum_embeddings_comp`), and `N_L(I𝓞_L) = N_K(I)^{[L:K]}` for fractional ideals
       (`absNorm_extendedHom`). Hence `deg_L((I, ρ)_{𝓞_L}) = [L:K]·deg_K(I, ρ)`
       (`arakelovDegree_ofFractionalIdeal_baseChange`): the normalized degree is invariant under
       base change, which is the Arakelov half of H4.
   - `torusMetricSq`, the archimedean Faltings metric `(i/2)^g∫_{ℂ^g/Λ} η∧η̄` of an invariant top
     form, with these properties:
     - it equals an integral over any fundamental domain (`torusMetricSq_eq_setIntegral`);
     - it does not depend on the linear coordinates (`torusMetricSq_comap`), via
       `covolume_comap_mul_det` and `det_ℝ = |det_ℂ|²`.
   - `HodgeData` packages an abelian variety given with a model and its uniformizations. On it:
     - `modelHeight`;
     - Faltings' formula for every nonzero `η` (`modelHeight_eq`);
     - independence of the coordinates (`modelHeight_recoord`);
     - the change-of-model formula `h(𝒢) = h(𝒢') + [K:ℚ]⁻¹ log[ω_𝒢 : ω_𝒢']` for
       `ω_𝒢' ⊆ ω_𝒢` (`modelHeight_eq_add_of_le`), and the monotonicity that makes the Néron
       lattice give the infimum (`modelHeight_le_of_le`).
   - **Acceptance test AT1 in conditional form**, for semistable elliptic curves of any class
     number (`modelHeight_ofIdeal_eq_faltingsHeightEC`; the free case is
     `modelHeight_eq_faltingsHeightEC`). The Hodge data has:
     - Néron lattice `𝔞·ω`;
     - Mathlib `PeriodPair` period lattices with `ω ↦ dz`.

     Under that data `modelHeight` equals pkg-I5's closed formula `faltingsHeightEC`, given two
     inputs:
     - the unproved classical identity `PeriodAreaFormula`,
       `covol(Λ) = 2∫_ℂ dλ/|4x³ − g₂x − g₃|`, checked numerically in pkg-I5;
     - the Néron identity `−12 log N(𝔞) = ∑_{v∤∞} log⁺|j|_v − ∑_σ log|σΔ|`, node AT1a.
   - `HodgeData` is inhabited (`exampleHodge`, the square lattice over `ℚ`; its height is 0 since
     `covol(ℤ + ℤi) = 1`, `exampleHodge_modelHeight_eq_zero`). This is a consistency check of the
     structure.
3. **The model layer typechecks over Mathlib today** (`Models.lean`, VERIFIED). `GroupModel A L`
   is a smooth, separated, quasi-compact group object in `Over (Spec 𝓞_L)` with an isomorphism of
   group objects from its generic fibre to `A_L`. It uses the project's `AbVar`, copied from
   `ZInQKernel/HDecomp/Objects.lean`.
   - What is missing between `GroupModel` and `HodgeData` is exactly three constructions:
     - AV3/M2, the cotangent lattice `e*Ω¹`;
     - AV4, its determinant (Mathlib has `exteriorPower` and its `finrank`);
     - AN3, the analytic uniformization.
4. **Size (SPECULATIVE).**
   - The definition without the uniformization: about 5-10k lines (AR3, AV2-AV5, M2-M4, H2-H4).
   - AN3: 15-30k lines.
   - The theorems that tie the definition to the literature (Néron models, semistable reduction,
     H5): each over 10k lines.
   - AT1 needs, in addition, elliptic curves as `AbVar`s. The project notes that Mathlib v4.35
     cannot yet build any nonzero `AbVar` (`Objects.lean`, docstring of `PkgI3.AbVar.zero`,
     VERIFIED).

   §5 recommends an order of work.

## 1. The definition and its normalizations (STANDARD)

Let `A/K` be an abelian variety of dimension `g` over a number field, `L/K` finite, and `𝒢/𝓞_L`
a smooth group model of `A_L`. Put `ω_𝒢 = e*Ω^g_{𝒢/𝓞_L} = ⋀^g e*Ω¹_{𝒢/𝓞_L}`, an invertible
`𝓞_L`-module inside the `L`-line `⋀^g H⁰(A_L, Ω¹)`. For `0 ≠ η ∈ ω_𝒢`:

`h(A_L, 𝒢) = [L:ℚ]⁻¹ ( log #(ω_𝒢/𝓞_L η) − ½ ∑_{σ:L→ℂ} log ((i/2)^g ∫_{A_σ(ℂ)} η∧η̄) )`.

- **Faltings' original normalization** is `(i/2)^g`. **Deligne's** is `(i/2π)^g`, giving
  `h_D = h_F + (g/2) log π`. Pazuki (R22) uses Deligne's normalization (h-decomposition R22).
  `torusMetricSq` uses Lebesgue measure on `ℂ = ℝ²`, which is `(i/2)dz∧dz̄`, so it is Faltings'
  original normalization. The sign convention: the positive value, i.e. `η∧η̄` reordered into
  `∏(dz_k∧dz̄_k)`.
- **Stable height.** `h_F^st(A) = h(A_L, 𝒩_L)` for any `L` over which `A` has semistable
  reduction, with `𝒩_L` the Néron model (Faltings 1983 §1; Deligne, Sém. Bourbaki 616; locators
  UNVERIFIED). It is independent of `L` because the identity component of the Néron model
  commutes with base change in the semistable case (SGA 7 IX 3.3, UNVERIFIED locator).
- **Infimum form (pkg-I5 §2.1).** `h_F^st(A) = inf_{L, 𝒢} h(A_L, 𝒢)`. Two facts give this:
  - every smooth `𝒢` maps to `𝒩_L` (Néron mapping property, BLR 1.2/1, UNVERIFIED), so
    `ω_{𝒩_L} ⊆ ω_𝒢` and `h(𝒢) ≥ h(𝒩_L)`; this inequality is `modelHeight_le_of_le`, BUILT;
  - `h(𝒩_L) ≥ h(𝒩_{L'}) = h^st` for `L'/L` semistable, again by the mapping property applied to
    `𝒩_L ×_{𝓞_L} 𝓞_{L'}`.
- **Recommendation: define the infimum in `EReal`** (or `WithBot ℝ`), not with `sInf` on `ℝ`.
  `sInf` of a set that is not bounded below is the junk value 0, and boundedness is a deep
  theorem (H5). Then prove `stableFaltingsHeight A ≠ ⊥, ≠ ⊤` in H5 and expose a real-valued
  `faltingsHeight A := (stableFaltingsHeight A).toReal` with that theorem attached.

## 2. Dependency graph

Tiers (SPECULATIVE, Lean lines): **S** ≤ 300, **M** 300-2 000, **L** 2 000-10 000,
**XL** > 10 000. Status: **Mathlib** = in Mathlib v4.35 (VERIFIED in `.lake/packages/mathlib`
unless marked); **project** = in this repository; **other** = another Lean library (from
prereq-survey, not re-checked); **lit** = only in the literature; **BUILT** = compiled here.

```
           NF0 (number fields)        MT0 (lattices, Haar)        AG0 (schemes, GrpObj, Smooth)
               │                            │                            │
          AR1 ─┴─ AR2 ──── AR3          AN1 ─ AN2                AV1 ─ AV2 ─ AV3 ─ AV4 ─ AV5
               │             │            │    │                  │            │
               │             │          AN3 (uniformization) ◄────┘            │
               │             │            │                                    │
               └─────────────┴──► H1 ◄────┘            M1 ─ M2 ─ M3 ◄──────────┘
                                   │                          │
                                   └──────────► M4 / H2 ◄─────┘
                                                 │
                                       H3 (infimum definition) ── H4 (base change)
                                                 │
                             H5 (= Néron value, finite) ◄── M5 (Néron) , M6 (semistable red.), M7
                                                 │
                          AT1 (elliptic) ◄── AV7, AN4, AN5        AT2 (genus 2) ◄── AV7, M8, AN6
                                                 │
                            leaves R18-R22 (also need AV6 isogenies, Jacobians, Belyi, theta)
```

### 2.1 Foundations already in Mathlib (VERIFIED)

| Node | Content | Where |
| --- | --- | --- |
| NF0 | `𝓞 K`, complex embeddings `K →+* ℂ`, `Algebra.norm`, `Ideal.absNorm` with `Ideal.absNorm_span_singleton`, `FractionalIdeal.absNorm`, `Algebra.norm_eq_prod_embeddings`, `InfinitePlace.prod_eq_abs_norm`, product formula (`NumberField/ProductFormula.lean`: `FinitePlace.prod_eq_inv_abs_norm`, `prod_abs_eq_one`), `AddSubgroup.relIndex_mul_relIndex`, `relIndex_map_map_of_injective` | `RingTheory/Ideal/Norm/AbsNorm.lean`, `NumberTheory/NumberField/*`, `GroupTheory/Index.lean` |
| MT0 | `ZLattice`, `ZLattice.covolume`, `covolume_eq_measure_fundamentalDomain`, `covolume_comap` (measure-preserving equivalences only), `ZLattice.isAddFundamentalDomain`, `IsAddFundamentalDomain.setIntegral_eq`, `Measure.map_linearMap_addHaar_eq_smul_addHaar`, `LinearMap.det_restrictScalars`, `Algebra.norm_complex_apply` | `Algebra/Module/ZLattice/*`, `MeasureTheory/Group/FundamentalDomain.lean`, `MeasureTheory/Measure/Lebesgue/EqHaar.lean`, `RingTheory/Norm/Transitivity.lean`, `RingTheory/Complex.lean` |
| AG0 | schemes, `Over`, `GrpObj` in `Over (Spec R)`, `Smooth`, `IsProper`, `IsSeparated`, `QuasiCompact`, `GeometricallyIntegral`, `Over.pullback` carrying group objects (`Functor.grpObjObj`), commutativity of proper geometrically integral group schemes (`isCommMonObj_of_isProper_of_geometricallyIntegral`), sheaves of modules on schemes with pullback (`AlgebraicGeometry/Modules/Sheaf.lean`) | `AlgebraicGeometry/*` |
| RT0 | Kähler differentials `Ω[A⁄R]`, projective for formally smooth algebras (`Algebra.FormallySmooth.projective_kaehlerDifferential`), `Ideal.Cotangent` (`I/I²`), `exteriorPower` `⋀[R]^n M` with `exteriorPower.finrank_eq` (`finrank = (finrank M).choose n`) | `RingTheory/Kaehler/*`, `RingTheory/Smooth/Basic.lean`, `RingTheory/Ideal/Cotangent.lean`, `LinearAlgebra/ExteriorPower/*` |
| AN0 | `PeriodPair`, its `lattice` (with `DiscreteTopology`, `IsZLattice ℝ` instances), `weierstrassP`, `derivWeierstrassP`, `g₂`, `g₃`, `derivWeierstrassP_sq` (`℘'² = 4℘³ − g₂℘ − g₃`); `LieGroup` (class only); the implicit function theorem (`HasStrictFDerivAt.implicitFunction`) | `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`, `Geometry/Manifold/Algebra/LieGroup.lean`, `Analysis/Calculus/Implicit.lean` |
| EC0 | `WeierstrassCurve`, `IsElliptic`, `j`, `Δ`; local minimal models `WeierstrassCurve.IsMinimal`, `exists_isMinimal`, reduction types (`HasGoodReduction`, `HasMultiplicativeReduction`, `HasAdditiveReduction`) | `AlgebraicGeometry/EllipticCurve/Weierstrass.lean`, `…/Reduction.lean` |

**Absent from Mathlib** (VERIFIED by search, Mathlib v4.35): sheaves of relative differentials
`Ω_{X/S}` on schemes; Néron models; semistable reduction of abelian varieties; analytification
(`X(ℂ)` as a complex manifold); the exponential map of Lie groups; integration of differential
forms on manifolds; any `AbelianVariety` definition, Lie algebra of a group scheme, Arakelov
theory or metrized line bundle.

### 2.2 Arakelov strand

| Node | Content | Tier | Status / route |
| --- | --- | --- | --- |
| AR1 | Hermitian line on `Spec 𝓞_K`: a rank-one `𝓞_K`-lattice `M` in a `K`-line `V`, norms `‖·‖_σ` with `‖a v‖_σ = |σa|‖v‖_σ` | S | **BUILT** `HermitianLattice` (§4) |
| AR2 | Arakelov degree `log #(M/𝓞s) − ∑_σ log‖s‖_σ`, independent of `s` | S | **BUILT** `arakelovDegree`, `degreeAt_eq_arakelovDegree`, `secIndex_smul`, `secIndex_ne_zero` |
| AR3 | Functoriality: `deg(M̄ ⊗ N̄) = deg M̄ + deg N̄`; base change `deg(M̄_{𝓞_L}) = [L:K]·deg(M̄)`; rescaling the metrics by `c_σ` shifts `deg` by `−∑ log c_σ` | M | **mostly BUILT**: rescaling (`arakelovDegree_rescale`); closed formula for fractional ideals (`secIndex_mul_absNorm`, `arakelovDegree_ofFractionalIdeal`); base change (`card_embeddings_over`, `sum_embeddings_comp`, `finrank_ringOfIntegers`, `absNorm_map_ringOfIntegers`, `norm_algebraMap_tower`, `absNorm_extendedHom`, `arakelovDegree_ofFractionalIdeal_baseChange`). Remaining: tensor products, and base change stated for an abstract `HermitianLattice`; that needs `L ⊗_K V`, or a reduction to the fractional-ideal form by choosing a section. Needed by H4 and additivity (E4b) |
| AR4 | (optional) Hermitian vector bundles of rank `g` and `deg := deg det` | M | not needed if one works with `det ω` from the start (recommended) |

### 2.3 Archimedean strand

| Node | Content | Tier | Status / route |
| --- | --- | --- | --- |
| AN1 | Faltings metric of `c·dz₁∧⋯∧dz_g` on `ℂ^g/Λ`: `|c|²·covol(Λ) = ∫_F |c|²` over any fundamental domain; integrals of periodic densities do not depend on `F` | S | **BUILT** `torusMetricSq`, `torusMetricSq_eq_setIntegral`, `torus_setIntegral_indep`, `torusMetricSq_pos` |
| AN2 | Independence of linear coordinates: `z = Tz'` sends `Λ ↦ T⁻¹Λ`, `c ↦ c·det T` | S | **BUILT** `torusMetricSq_comap` (with `covolume_comap_mul_det`, `det_restrictScalars_complex`) |
| AN3 | **Uniformization.** For `A : AbVar ℂ` of dimension `g`: a lattice `Λ ⊂ Lie(A) ≅ ℂ^g` with `A(ℂ) ≅ Lie(A)/Λ` as complex Lie groups, and the identification of invariant top forms with `c·dz₁∧⋯∧dz_g` | XL | **lit** (Mumford, *Abelian varieties* §1; Serre GAGA). Route (a), recommended: (i) the analytic topology and a complex-manifold structure on `X(ℂ)` for `X` smooth of finite type over `ℂ`, from étale coordinates and the holomorphic implicit function theorem (Mathlib has the real/complex implicit function theorem and charted spaces); (ii) `X` proper ⇒ `X(ℂ)` compact (needs the valuative criterion over `ℂ` or Chow's lemma in the analytic setting); (iii) a compact connected commutative complex Lie group is `ℂ^g/Λ` (one-parameter subgroups by ODE flows, Mathlib's `IsIntegralCurve` existence; `exp` is a surjective homomorphism with discrete kernel). Route (b): for Jacobians only, Abel-Jacobi with path integrals on the Riemann surface; still needs (i) for curves. Milestone that already unblocks AN1-H2: (i)+(iii) without GAGA |
| AN4 | `g = 1`: every elliptic `W/ℂ` is `ℂ/Λ` for a `PeriodPair` with `η₀ = dx/(2y + a₁x + a₃) ↦ dz`, and then `P_W = 4x³ − g₂x − g₃` after completing the square (Silverman AEC VI 5.1, UNVERIFIED) | L | **lit**; Mathlib has `℘` and its differential equation, not surjectivity of `j` or the group isomorphism. A special case of AN3 that is cheaper by itself |
| AN5 | **Area formula** `covol(Λ) = 2∫_ℂ dλ/|4x³ − g₂x − g₃|` | M | stated as `PeriodAreaFormula` (Prop, **unproved**). Route: `℘ : ℂ/Λ∖{0} → ℂ` is 2:1 with `d℘ = ℘'dz`, `|℘'|² = |P(℘)|`; split a fundamental domain into two halves exchanged by `z ↦ −z` and use `integral_image_eq_integral_abs_det_fderiv_smul` on each. Numerical check: pkg-I5 `area_check.py` (VERIFIED there) |
| AN6 | `g = 2` (hyperelliptic): `(i/2)²∫_{Jac C}|ω₀∧ω₁|² = det((i/2)∫_C ωᵢ∧ω̄ⱼ)` (Riemann bilinear relations) | L | **lit**; needs the Jacobian's period lattice (AN3 or route (b)). pkg-I5 `hypVol` is the right-hand side |

### 2.4 Algebraic-geometry strand (over fields)

| Node | Content | Tier | Status / route |
| --- | --- | --- | --- |
| AV1 | `AbVar K`: group object in `Over (Spec K)`, proper, smooth, geometrically integral | S | **project** `ZInQKernel/HDecomp/Objects.lean` (`AbVar`, `IsAbelianVariety`, `IsAbelianScheme`); **other**: Tau Ceti `TauCeti.AlgebraicGeometry.AbelianVariety` (definitions); copied into `Models.lean` |
| AV2 | Dimension `g : ℕ` (relative dimension of the smooth structure map; the project's `AbVar.dim` is a `WithBot ℕ∞` Krull dimension) | S-M | route: Mathlib's `SmoothOfRelativeDimension`, plus the identification with Krull dimension |
| AV3 | Invariant differentials `ω_A = e*Ω¹_{A/K}`, a `K`-space of dimension `g` | M-L | route (i), recommended: `Ideal.Cotangent` of the maximal ideal of the stalk at the `K`-point `e`, i.e. `𝔪/𝔪²`, with dimension `g` from smoothness (a regular local ring of dimension `g`); route (ii): sheaf `Ω_{X/S}` on schemes by gluing `Ω[A⁄R]` (L, absent); route (iii): `Lie(A) = ker(A(K[ε]) → A(K))` with `DualNumber` (the module structure is the hard part) |
| AV4 | The `K`-line `V = ⋀^g ω_A` | S | Mathlib `exteriorPower`, `exteriorPower.finrank_eq` (VERIFIED) |
| AV5 | Base change: `A_L` (**project** `PkgI3.AbVar.baseChange`, copied into `Models.lean`) and `ω_{A_L} = L ⊗_K ω_A` | M | route: cotangent spaces commute with flat base change |
| AV6 | Products `A × B` with `ω_{A×B} = ω_A ⊕ ω_B`; isogenies and their degree | M-L | **project** `IsIsogenyMor`; **other**: Tau Ceti `IsIsogeny` (definition only). Needed by R19, R20, additivity |
| AV7 | Construct actual abelian varieties: elliptic curves as `AbVar` (projective Weierstrass scheme with the group law as scheme morphisms); Jacobians of curves | L (EC) / XL (Jacobians) | **absent**. The project notes that no nonzero `AbVar` can be constructed in Mathlib v4.35 (VERIFIED, `Objects.lean`). **other**: Anthropic FLT has Jacobians in a special case (prereq-survey). Needed by AT1, AT2, R18 |

### 2.5 Model strand

| Node | Content | Tier | Status / route |
| --- | --- | --- | --- |
| M1 | `GroupModel A L`: smooth, separated, quasi-compact group object of `Over (Spec 𝓞_L)` with an isomorphism of group objects `𝒢_L ≅ A_L` | S | **BUILT** `Models.lean` (`GroupModel`, `genericFibre`) |
| M2 | `ω_𝒢 = e*Ω¹_{𝒢/𝓞_L}`, a projective `𝓞_L`-module of rank `g`, and `ω_𝒢 ⊗ L ≅ ω_{A_L}` via `gen` | M-L | route: the conormal module `I/I²` of the unit section (a closed immersion since `𝒢` is separated), computed on an affine open containing `e(Spec 𝓞_{L,𝔭})` locally on `Spec 𝓞_L`; projectivity of rank `g` from `Algebra.FormallySmooth.projective_kaehlerDifferential` and smoothness of relative dimension `g` |
| M3 | `det ω_𝒢 ⊆ V_L` with the `isLattice` field of `HodgeData` | S | from M2 (`secIndex` is finite for a rank-one lattice) |
| M4 | `GroupModel.hodgeData : HodgeData L g V_L`, assembling M3 and AN3 at every `σ : L → ℂ` | S | signature in `Models.lean` (comment) |
| M5 | Néron models over Dedekind `𝓞_L`: existence and the mapping property | XL | **lit** (Néron 1964; BLR 1.4/3, UNVERIFIED). **other**: Anthropic FLT, Néron models in a special case (prereq-survey). **Not needed for the definition** |
| M6 | Grothendieck's semistable reduction theorem (SGA 7 IX 3.6) | XL | **lit**; only for elliptic curves elsewhere (Tau Ceti). Not needed for the definition |
| M7 | Semistable Néron models: the identity component commutes with base change (SGA 7 IX 3.3, UNVERIFIED) | XL | **lit**. Needed for H5 |
| M8 | Néron model of `Jac C` for smooth proper `𝒞/𝓞_L` is `Pic⁰_{𝒞/𝓞_L}`, with `ω = H⁰(𝒞, ω_𝒞)` (BLR 9.5 Thm 4; Liu; UNVERIFIED) | XL | **lit**. Needed by AT2 |

### 2.6 The height

| Node | Content | Tier | Status / route |
| --- | --- | --- | --- |
| H1 | `HodgeData.modelHeight = deg(ω̄)/[K:ℚ]` and Faltings' formula for every `η` | S | **BUILT** `modelHeight`, `modelHeight_eq`, `modelHeight_of_span` |
| H2 | `GroupModel.height`: independent of every choice inside it | S | **BUILT** for the section `η` (`modelHeight_eq`), the fundamental domain (AN1), the linear coordinates on `Lie(A_σ)` (`modelHeight_recoord`); the basis of `Λ` plays no role (`Λ` is a set) |
| H3 | `stableFaltingsHeight A : EReal := ⨅ L 𝒢, 𝒢.height` | S | signature in `Models.lean` (comment). The index type "finite extensions `L/K` with a `K`-embedding" should be a structure in one universe (e.g. intermediate fields of `AlgebraicClosure K`, or `Type` with `[Algebra K L] [FiniteDimensional K L]`) |
| H4 | Base change of models: `𝒢 ×_{𝓞_L} 𝓞_{L'}` is a model of `A_{L'}` (Mathlib: smoothness, separatedness, quasi-compactness are stable under base change) with the same height | M | from AR3 and AV5 and the compatibility of `ω_𝒢` with flat base change. **BUILT** at the level of Hodge data of dimension 1: `HodgeData.modelHeight_ofIdeal_baseChange` (from `arakelovDegree_ofFractionalIdeal_baseChange`) |
| H5 | `stableFaltingsHeight A` is finite and equals `𝒩_L.height` for semistable `L`; independent of `K` (`h(A_L) = h(A)`) | XL | from M5-M7 and `modelHeight_le_of_le` (**BUILT**) |
| H6 | Deligne normalization `h_D = h_F + (g/2) log π` | S | definitional |
| H7 | Additivity `h(A × B) = h(A) + h(B)` (E4b) | M | from AV6, AR3 and the covolume of a product lattice |

### 2.7 Acceptance tests

These guard against a vacuous or mis-normalized definition (pkg-I5 §5). Their right-hand sides
compile (pkg-I5 `faltingsHeightEC`, `faltingsHeightGood`, copied into `Hodge.lean`).

| Test | Statement | Needs | Status |
| --- | --- | --- | --- |
| AT1 | `faltingsHeight (ellipticCurve W) = faltingsHeightEC W` for every elliptic `W` over a number field | AV7 (EC as `AbVar`), AN4, AN5; for the Néron lattice: AT1a below; general `W` via H5 and base change to a semistable field | **conditional form BUILT**: `modelHeight_ofIdeal_eq_faltingsHeightEC` proves `modelHeight = faltingsHeightEC` from `PeriodAreaFormula` (AN5), the Weierstrass-polynomial match (AN4) and the Néron identity (AT1a); free special case `modelHeight_eq_faltingsHeightEC`; any Weierstrass model (translation at each `σ`) `modelHeight_ofIdeal_eq_faltingsHeightEC'` |
| AT1a | For `W` with semistable reduction everywhere, the Néron lattice is `𝔞·dx/(2y + a₁x + a₃)` with `ord_𝔭 𝔞 = (ord_𝔭 Δ − ord_𝔭 Δ_min)/12`, and `−12 log N(𝔞) = ∑_{v∤∞} log⁺|j|_v − ∑_σ log|σΔ|`, because `ord_𝔭 Δ_min = max(0, −ord_𝔭 j)` and by the product formula | Néron model of an elliptic curve = smooth locus of the minimal Weierstrass model (Silverman AEC II IV.6; BLR 1.5/1; UNVERIFIED locators); Mathlib's `IsMinimal`; the product-formula step is Mathlib (`NumberField/ProductFormula.lean`) | **lit** for the Néron step; the identity is the hypothesis `hNeron` of the bridge |
| AT2 | `faltingsHeight (jacobian C) = faltingsHeightGood E` for genus-2 equations with `2⁻¹²disc₆` a unit | AV7 (Jacobians), M8, AN6 | **lit**; statement compiles in pkg-I5 |
| AT3 | Numerical: `faltingsHeightEC` at `j = 0` gives `−1.321117`, Deligne's minimum shifted by `−½ log π`; 11a1 and 11a3 differ by `½ log 5` | — | **VERIFIED** in pkg-I5 (`ec_height_check.py`) |

### 2.8 What each leaf R18-R22 needs beyond the height

Templates: pkg-I5 §3. Everything below is stated over `faltingsHeight A` for a genuine
`A : AbVar K`, never over `HodgeData` (§4.3).

| Leaf | Extra objects | Nodes |
| --- | --- | --- |
| R18 Javanpeykar | smooth projective curves over number fields, genus, Jacobian, Belyi degree, `X₁(N)` | AV7 (Jacobians), plus curve infrastructure |
| R19 Gaudron-Rémond | isogenies, their degree, `[K:ℚ]` | AV6 |
| R20 Faltings Lemma 5 | isogenies, degree | AV6 |
| R21 Bost | `dim` | AV2 |
| R22 Pazuki | principally polarized abelian surfaces, level-2 theta structure, theta height; Deligne normalization | H6, polarizations (Anthropic FLT `PolarisedAbelianScheme`, prereq-survey) |

## 3. Independence of choices: where each is proved

| Choice | Where it is handled |
| --- | --- |
| the section `η ∈ ω_𝒢` | `HermitianLattice.degreeAt_eq_arakelovDegree` (**BUILT**), via the product formula `sum_log_norm_embeddings` and `secIndex_smul` |
| the fundamental domain of `Λ_σ` | `torusMetricSq_eq_setIntegral`, `torus_setIntegral_indep` (**BUILT**) |
| the linear coordinates on `Lie(A_σ)` | `torusMetricSq_comap`, `HodgeData.modelHeight_recoord` (**BUILT**) |
| the model `𝒢` over a fixed `L` | by the infimum (H3); the comparison of two nested models is `modelHeight_eq_add_of_le` (**BUILT**); that the Néron model is the minimum: M5 + `modelHeight_le_of_le` |
| the field `L` | H4 (base change of a model keeps the height; M; the Arakelov part is **BUILT**: `arakelovDegree_ofFractionalIdeal_baseChange`, `HodgeData.modelHeight_ofIdeal_baseChange`) and H5 (semistable invariance; XL) |
| the embedding `K → L` | built into the index type of H3 |

## 4. What compiles (VERIFIED)

`lake env lean scratch/bp-faltings/Hodge.lean` and `lake env lean scratch/bp-faltings/Models.lean`
report no errors and no warnings. `#print axioms` on every main theorem lists `propext`,
`Classical.choice`, `Quot.sound`. Mathlib only; no project imports.

### 4.1 `Hodge.lean`

| § | Declarations | Content |
| --- | --- | --- |
| 1 | `sum_log_norm_embeddings`, `sum_log_norm_embeddings_int` | `∑_{σ:K→ℂ} log‖σx‖ = log|N_{K/ℚ}x|` |
| 2 | `secIndex`, `secIndex_smul`, `HermitianLattice`, `degreeAt`, `degreeAt_smul`, `exists_smul_eq`, `secIndex_ne_zero`, `degreeAt_eq`, `arakelovDegree`, `degreeAt_eq_arakelovDegree` | AR1, AR2 |
| 3 | `covolume_comap_mul_det`, `det_restrictScalars_complex`, `torusMetricSq`, `torusMetricSq_eq_setIntegral`, `torus_setIntegral_indep`, `torusMetricSq_pos`, `torusMetricSq_smul`, `realify`, `torusMetricSq_comap` | AN1, AN2 |
| 4 | `HodgeData`, `coeff_apply_ne_zero`, `norm`, `norm_sq`, `hodgeBundle`, `modelHeight`, `modelHeight_eq`, `recoord`, `modelHeight_recoord`, `modelHeight_eq_add_of_le`, `modelHeight_le_of_le` | H1, H2 (in part), the model comparison used by H5 |
| 5 | `hypGram`, `hypVol`, `finiteHeightPart`, `faltingsHeightEC` (copied from pkg-I5), `modelHeight_of_span`, `PeriodPair.lattice1`, `PeriodPair.covolume_lattice1`, `PeriodAreaFormula` (Prop), `modelHeight_eq_faltingsHeightEC` | AT1, conditional form (free lattice) |
| 6 | `HermitianLattice.rescale`, `arakelovDegree_rescale`, `gaussianPair`, `ratCoeff`, `exampleHodge`, `exampleHodge_modelHeight` | AR3 (rescaling); `HodgeData` is inhabited |
| 7 | `secIndex_mul_absNorm`, `HermitianLattice.ofFractionalIdeal`, `arakelovDegree_ofFractionalIdeal` | AR3 (fractional ideals) |
| 8 | `embCoeff`, `HodgeData.ofIdeal`, `HodgeData.modelHeight_ofIdeal`, `modelHeight_ofIdeal_eq_faltingsHeightEC` | AT1, conditional form (any Néron lattice `𝔞·ω`) |
| 9 | `card_embeddings_over`, `sum_embeddings_comp` | AR3 / H4 (archimedean half of base change) |
| 10 | `hypGram_comp_add`, `hypVol_one_comp_add`, `modelHeight_ofIdeal_eq_faltingsHeightEC'` | AT1 for every Weierstrass model: `P_W^σ` need only equal `4x³ − g₂x − g₃` after a translation `x ↦ x + c_σ` (`ω ↦ dz` fixes `g₂ = c₄/12`, `g₃ = c₆/216`; `b₂` is removed by translation) |
| 11 | `finrank_ringOfIntegers`, `absNorm_map_ringOfIntegers`, `norm_algebraMap_tower`, `absNorm_extendedHom`, `arakelovDegree_ofFractionalIdeal_baseChange` | AR3 (base change: `deg_L = [L:K]·deg_K`) |
| 12 | `HodgeData.modelHeight_ofIdeal_baseChange` | H4 for dimension-1 Hodge data: extending the lattice to `𝓞_L` and restricting the period lattices leaves the model height unchanged |
| 13 | `covolume_gaussianPair`, `exampleHodge_modelHeight_eq_zero` | normalization check: `covol(ℤ + ℤi) = 1` for Mathlib's Lebesgue measure on `ℂ`, so the example has height 0 |

Key statements (Lean, abridged):

```lean
theorem secIndex_smul (M : Submodule (𝓞 K) V) {s : V} (hsM : s ∈ M) (hs : s ≠ 0) (a : 𝓞 K) :
    secIndex M (a • s) = (Algebra.norm ℤ a).natAbs * secIndex M s
theorem HermitianLattice.degreeAt_eq_arakelovDegree {s : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0) :
    L.degreeAt s = L.arakelovDegree
theorem covolume_comap_mul_det (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] E) :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) μ * |LinearMap.det e.toLinearMap|
      = ZLattice.covolume L μ
theorem torusMetricSq_comap (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (c : ℂ) :
    torusMetricSq (ZLattice.comap ℝ Λ (realify T).toLinearMap) (c * LinearMap.det T)
      = torusMetricSq Λ c
theorem HodgeData.modelHeight_eq {η : V} (hηM : η ∈ D.lattice) (hη : η ≠ 0) :
    D.modelHeight = (Real.log (secIndex D.lattice η) -
      (1/2) * ∑ σ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ η))) / finrank ℚ K
theorem HodgeData.modelHeight_eq_add_of_le (D' : HodgeData K g V) (hp : D'.periods = D.periods)
    (hc : D'.coeff = D.coeff) (hle : D'.lattice ≤ D.lattice) :
    D.modelHeight = D'.modelHeight +
      Real.log (D'.lattice.toAddSubgroup.relIndex D.lattice.toAddSubgroup) / finrank ℚ K
theorem secIndex_mul_absNorm (I : FractionalIdeal (𝓞 K)⁰ K) {x : K} (hx : x ∈ I) (hx0 : x ≠ 0) :
    (secIndex (I : Submodule (𝓞 K) K) x : ℚ) * FractionalIdeal.absNorm I = |Algebra.norm ℚ x|
theorem sum_embeddings_comp (f : (K →+* ℂ) → ℝ) :
    ∑ τ : L →+* ℂ, f (τ.comp (algebraMap K L)) = finrank K L * ∑ σ : K →+* ℂ, f σ
def PeriodAreaFormula : Prop :=
  ∀ L : PeriodPair, ZLattice.covolume L.lattice = hypVol 1 (4 * X ^ 3 - C L.g₂ * X - C L.g₃)
theorem modelHeight_ofIdeal_eq_faltingsHeightEC (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃)
    (hNeron : -12 * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) =
      finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight = faltingsHeightEC W
```

### 4.2 `Models.lean`

`AbVar`, `AbVar.baseChange` (copied), `genericFibre`, `GroupModel` (node M1), and two sanity
examples: the generic fibre of a model is smooth and separated. The file ends with the
uncompiled signatures of AV2-AV4, M2-M4 and H2-H3 that the team builds against.

### 4.3 How `HodgeData` must and must not be used

`HodgeData` is **internal plumbing**: its fields (lattice, period lattices, coefficient maps) are
what nodes AV3/M2/M3 and AN3 *produce* from a genuine `GroupModel`. It is not an object over
which a leaf may be stated. A leaf stated over an arbitrary `HodgeData` would quantify over fake
period lattices and fake lattices, and would be false or vacuous; this is the failure mode of
wk-h's `ArakelovSig` noted in pkg-I5 §5. The theorems proved here are true for **every**
`HodgeData`, so they transfer to `GroupModel.hodgeData` with no further work. Likewise
`modelHeight_eq_faltingsHeightEC` is a bridge lemma with explicit hypotheses, not a leaf; its
hypotheses are exactly the outputs of AN4, AN5 and AT1a.

## 5. Recommended order of work for the crowdsourced team

1. **WP-A (S-M, can start now).** Finish AR3: tensor products, and base change for an abstract
   `HermitianLattice` (the fractional-ideal case is BUILT here), and H6. Pure Mathlib.
2. **WP-B (M, can start now).** AN5 (`PeriodAreaFormula`) from Mathlib's `℘`. This turns AT1's
   archimedean half into a theorem.
3. **WP-C (M-L).** AV2-AV5 and M2-M3: dimension, cotangent spaces, `e*Ω¹` of a smooth group
   model as a rank-`g` projective `𝓞_L`-module, its determinant, and base change (H4).
4. **WP-D (XL, the critical path).** AN3: analytification of smooth `ℂ`-schemes and the torus
   theorem. Route (a) of §2.3. Until it exists, `GroupModel.height` cannot be defined. The
   leaves can still be drafted against the signature `AbVar.periodData`.
5. **WP-E (L-XL).** AV7: elliptic curves as `AbVar`s (needed for AT1 and to have any nonzero
   abelian variety at all), then Jacobians (AT2, R18).
6. **WP-F (XL, not needed to state the leaves).** M5-M7 and H5: Néron models, semistable
   reduction, finiteness of the infimum and equality with the Néron value.

The leaves R18-R22 become faithful Lean statements after WP-C + WP-D (definition) plus the
leaf-specific objects of §2.8. Confidence that the definition is the published one comes from
AT1/AT2 (WP-B, WP-E and AT1a) and, fully, from WP-F.

## 6. Unchecked items (UNVERIFIED or not done)

1. Locators recalled from memory: BLR 1.2/1 (Néron mapping property), 1.4/3 (existence), 1.5/1,
   9.5 Thm 4; SGA 7 IX 3.3, 3.6; Silverman AEC VI 5.1 and AEC II IV.6; Deligne, Sém. Bourbaki
   616; Faltings 1983 §1.
2. Not built: tensor products and abstract base change in AR3; H4, H7, AN3-AN6,
   AV2-AV7, M2-M8, H3 (signature only), H5; the proof of `PeriodAreaFormula`; the identity
   AT1a.
3. Library items cited from prereq-survey and not re-checked: Tau Ceti `AbelianVariety`,
   `IsIsogeny`; Anthropic FLT Néron models, Jacobians and `PolarisedAbelianScheme`.
4. The size tiers and the line estimates are SPECULATIVE.
