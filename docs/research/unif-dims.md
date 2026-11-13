# unif-dims: `ProductUnifDims` proved from T35; `ProductHodgeLattice` reduced to one geometric Prop

Status: research note (task unif-dims, 2026-11-13).
- **Lean:** `scratch/unif-dims/`. Every file below compiles with `lake env lean`, with no `sorry`
  and no `axiom`, and every `#print axioms` lists only `propext`, `Classical.choice` and
  `Quot.sound` (VERIFIED, see `scratch/unif-dims/log.md`).
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited. Merged: origin/wip/product-unif.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = estimate or unchecked argument. **UNVERIFIED** =
locator from memory (no network).

## 0. Main results

1. **`ZInQ.ProductUnif.ProductUnifDims` is proved from the textbook leaf T35** (VERIFIED):

   ```lean
   theorem ZInQ.UnifDims.productUnifDims_of_uniformizationExists
       (hT : ZInQ.LeafPush2.UniformizationExists) : ZInQ.ProductUnif.ProductUnifDims
   ```

   T35 (`UniformizationExists`, Mumford §1 with GAGA) is already `TextbookLeaves.t35`, so this adds
   no leaf and no glue. The proof has two halves.
   - **Dimension half** (`ProductUnifDimsEq`). The dimension of an analytic uniformization is fixed
     by the abstract group `𝒢(ℂ)_τ`. If `Φ : ℂ^g → G` is an onto homomorphism whose kernel is a
     discrete full `ℤ`-lattice `Λ`, then `#{p ∈ G : p² = 1} = 2^{2g}`.
     - Proof: `λ ↦ Φ(λ/2)` maps `Λ` onto `G[2]` with kernel `2Λ`, and `[Λ : 2Λ] = 2^{rank Λ}`
       with `rank Λ = 2g`. The Lean names are `card_twoTorsion` and `dim_eq_of_unif`, in
       `Torsion.lean`, which uses Mathlib only.
     - T35, transported to group models by metrization2's
       `analyticUniformizationOfDim_of_uniformizationExists`, gives one uniformization of dimension
       `dim A`. So every full-lattice analytic uniformization has `g = dim A`
       (`dim_eq_of_isAnalyticUniformization`).
     - Only the algebraic clauses of `IsAnalyticUniformization` are used (homomorphism, kernel,
       onto).
   - **Nonsingularity half.** This is metrization2's `jacDetNondegenerate`, proved with no
     hypotheses. product-unif's `productUnifDims_of` already combined the two halves.
   - The product structure and the metrization `MP` in the hypotheses of `ProductUnifDims` are not
     used. The statement is therefore true but stronger in its hypotheses than it needs to be
     (§2).

2. **metrization's `ProductHodgeLattice` is reduced to one new geometric glue Prop**
   (VERIFIED). infra-stalks had not closed it: origin/wip/infra-stalks 7667e59b has stalk
   infrastructure only.

   ```lean
   theorem ZInQ.UnifDims.productHodgeLattice_of_cotangent (hPC : ProductCotangent)
       (hT : ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin)
       (hT35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.ProductHodgeLattice
   ```

   - **`ProductCotangent`** (new glue, algebraic geometry, open). The cotangent space at the
     generic unit of a product model is `j₁(cot₁) ⊕ j₂(cot₂)`, where `jᵢ(df) = d(pᵢ* f)`. The
     conormal lattice is `ω_P = j₁ω₁ + j₂ω₂`.
   - **`DetLatticeProd`** (new glue, pure commutative algebra) is **proved**:
     `ZInQ.UnifDims.detLatticeProd`, in `DetProd.lean`. For `M₁ × M₂ ≅ M` over `𝓞_K` with
     f.g. full lattices `ωᵢ` of ranks `gᵢ`, the determinant lattice of `j₁ω₁ + j₂ω₂` has a section
     whose index is the product of the factors' indices.
   - `TangentDimAtOrigin` is hodge-lattice's open Prop, which is already named. It reduces to
     `RegularAtOrigin` and `DimAtOrigin` (`tangentDimAtOrigin_of`).
   - hodge-lattice's other input `DimBaseChange` is proved here (`dimBaseChange`, from g0-dim's
     `G0Dim.dim_baseChange`).
   - T35 is used only for `gᵢ = dim` of the two metrizations.

3. **Consequence for S-alg and for glue piece 5 (P2)** (VERIFIED, `Combined.lean`):

   ```lean
   theorem ZInQ.UnifDims.productMetrizationOfProductUnif_of_cotangent
       (hT35 : ZInQ.LeafPush2.UniformizationExists) (hPC : ProductCotangent)
       (hT : TangentDimAtOrigin) : ZInQ.ProductHeight.ProductMetrizationOfProductUnif
   theorem ZInQ.UnifDims.productModelHeight_of_cotangent
       (hT35 : ZInQ.LeafPush2.UniformizationExists) (hPC : ProductCotangent)
       (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight
   ```

   The proof combines four things:
   - product-unif's `productModelHeight_of_local`, which needs `HodgeLatticeTheorem`,
     `ProductUnifDims`, `ProductLocalStructure` and `ProductHodgeLattice`;
   - hodge-lattice's `hodgeLatticeTheorem_of_tangent`;
   - metrization2's `productLocalStructure` (proved);
   - items 1 and 2.

   So `GluePieces.productModelHeight` (P2) rests on:
   - the existing leaf T35;
   - the already-named open Prop `TangentDimAtOrigin`, shared with `HodgeLatticeTheorem`, hence
     with `MetrizationExists`;
   - the single new geometric glue Prop `ProductCotangent`.

4. **No statement is false, vacuous or inert.**
   - `ProductUnifDims` is true (item 1 proves it from a true leaf).
   - `ProductHodgeLattice` is true: it is a consequence of `ProductCotangent` and
     `TangentDimAtOrigin`, which are true (STANDARD), and of T35.
   - An independent read-only model review checked `ProductCotangent`, `DetLatticeProd` and the
     statement of `productHodgeLattice_of`. Verdict: both Props are TRUE for every instance, not
     vacuous, and not disguised forms of the conclusion, and the reduction is faithful. The
     reviewer also diffed `ProductHodgeLattice` and `pullGerm` against `scratch/metrization` and
     found them identical. `DetLatticeProd` has since been proved.

## 1. Files (all VERIFIED: compile, standard axioms only)

| file | imports | content |
|---|---|---|
| `Torsion.lean` | Mathlib | `halfHom`, `card_twoTorsion` (`#G[2] = 2^{2g}`), `dim_eq_of_unif` |
| `DetProd.lean` | `ZInQKernel.HDecomp.Faltings.HodgeLattice` | `detFun`, `detFun_injective`, `exists_basis_of_span`, `secIndex_map`, `secIndex_one_mul`, `sumIso`, `prodBasis`, `det_prodBasis_append`, `card_le_of_li_range`, **`detLatticeProd_aux`** |
| `UnifDims.lean` (generated by `build.sh`) | `LeafPush2.T`, `HodgeLattice`, Mathlib | metrization2's `Kernel.lean` (verbatim copy in `base/`), product-unif §0 and `ProductUnifDims`, `ProductUnifDimsEq`, `productUnifDims_of` (verbatim), `pullGerm` and `ProductHodgeLattice` (verbatim), Torsion, DetProd, `part_main.lean`, `part_phl.lean`, `part_final.lean`; 15 s |
| `Combined.lean` (generated by `build_combined.py`) | `H5Neron`, `LeafPush2.T`, `HodgeLattice`, Mathlib | product-unif's `WithProductHeight.lean` (product-height's own `ProductHeight.lean` + ProductUnif §1-§4) + metrization2's kernel file (its duplicates of ProductUnif's metrization copies removed) + this task's parts + `part_combined.lean`; 22 s |

Main declarations (namespace `ZInQ.UnifDims`):

| name | statement |
|---|---|
| `dim_eq_of_isAnalyticUniformization` | `AnalyticUniformizationOfDim →` a full-lattice analytic uniformization `ℂ^g → 𝒢(ℂ)_τ` has `A.dim = g` |
| `productUnifDimsEq_of` | `AnalyticUniformizationOfDim → ProductUnifDimsEq` |
| `productUnifDims_of_unifOfDim`, **`productUnifDims_of_uniformizationExists`** | `ProductUnifDims` from `AnalyticUniformizationOfDim`, from T35 |
| `ProductCotangent`, `DetLatticeProd` | new glue Props (§3) |
| `dimBaseChange` | hodge-lattice's `DimBaseChange` |
| `rank_tensor_of_bijective` | `rank_K (K⊗M) = g₁ + g₂` for `M₁ × M₂ ≅ M` |
| `productHodgeLattice_of` | `ProductCotangent → DetLatticeProd → CotangentRank → AnalyticUniformizationOfDim → ProductHodgeLattice` |
| `productHodgeLattice_of_tangent` | the same with `TangentDimAtOrigin` and T35 |
| **`detLatticeProd`** | `DetLatticeProd` |
| **`productHodgeLattice_of_cotangent`** | `ProductCotangent → TangentDimAtOrigin → T35 → ProductHodgeLattice` |
| **`productMetrizationOfProductUnif_of_cotangent`**, **`productModelHeight_of_cotangent`** | S-alg and P2 from T35, `ProductCotangent`, `TangentDimAtOrigin` |

## 2. `ProductUnifDims`: how, and a remark on its statement

- `card_twoTorsion` proceeds in four steps.
  1. `ZLattice.rank` gives `finrank_ℤ Λ = finrank_ℝ ℂ^g = 2g`.
  2. `finBasisOfFinrankEq` gives a `ℤ`-basis.
  3. The kernel of `λ ↦ Φ(λ/2)` is the preimage of `∏ 2ℤ` under the coordinate equivalence, so
     its index is `2^{2g}` (`AddSubgroup.index_comap_of_surjective`, `AddSubgroup.index_pi`,
     `Int.index_zmultiples`).
  4. `QuotientAddGroup.quotientKerEquivRange` identifies the quotient with `G[2]`.
- The remark (not a defect). `ProductUnifDims` assumes a product-form metrization `MP`, but its
  conclusion holds for any two full-lattice analytic uniformizations `Φ₁`, `Φ₂` of the factors,
  once T35 is available. In the reduction of S-alg, `ProductUnifDims` could therefore be replaced
  by T35, which is already a leaf. Without T35 the dimension half would need the Krull dimension
  of `A` from complex-analytic data, which is not available.

## 3. `ProductHodgeLattice`: the decomposition

| name | kind | statement (short) | status |
|---|---|---|---|
| `Metrization.ProductHodgeLattice` | glue (target) | for `e : 𝒢P ≅ M₁.model × M₂.model`: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line; germ tuples `f₁, f₂`, `f = (p₁*f₁, p₂*f₂)` and `a₁, a₂` give nonzero sections with `[⋀ω_P : 𝓞s] = [⋀ω₁ : 𝓞s₁][⋀ω₂ : 𝓞s₂]` | **reduced** |
| `UnifDims.ProductCotangent` | **new glue** (algebraic geometry) | `𝓞_L`-linear `jᵢ : cotᵢ → cot_P` with `jᵢ(df) = d(pᵢ* f)` (`pᵢ* = pullGerm`, and `pᵢ* f ∈ 𝔪_P`); `(x,y) ↦ j₁x + j₂y` bijective; `ω_P = j₁ω₁ ⊔ j₂ω₂` | open. Why true (STANDARD): `𝒪_{𝒢P,ξ}` is the local ring of `A_L × B_L` at the origin; `Ω_{X×_S Y} = p₁*Ω_X ⊕ p₂*Ω_Y`; at each `s`, the ideal of the product section is `p₁*I₁ + p₂*I₂` (kernel of `R₁ ⊗ R₂ → 𝓞`), and the intersection over `s` commutes with the direct sum (EGA IV 16.4.23 / Stacks, UNVERIFIED locators) |
| `UnifDims.DetLatticeProd` | glue (commutative algebra) | determinant lattice of `j₁ω₁ ⊕ j₂ω₂`: a section `s = s₁ ∧ s₂` with multiplicative index | **proved** |
| `HodgeLattice.CotangentRank` | glue (kernel) | `rank_L (L ⊗ cot) = dim A` | reduced by hodge-lattice to `TangentDimAtOrigin` + `DimBaseChange` |
| `HodgeLattice.TangentDimAtOrigin` | glue (kernel, open) | the tangent space of `B/L` at the origin has dimension `dim B` | open (STANDARD; needs the dimension theory of varieties) |
| `HodgeLattice.DimBaseChange` | glue (kernel) | `dim A_L = dim A` | **proved** here from g0-dim |
| `LeafPush2.UniformizationExists` (T35) | leaf (textbook, in `TextbookLeaves`) | uniformization of `A(ℂ)_σ` by `ℂ^{dim A}` | leaf |

How `DetLatticeProd` is proved (`DetProd.lean`, about 450 lines):
1. **Bases and determinant functionals.**
   - Pick `𝓞_K`-families `wᵢ` in `ωᵢ` with `1 ⊗ wᵢ` a `K`-basis `bᵢ` of `K ⊗ Mᵢ` (hodge-lattice's
     step 1). Concatenate them through `K⊗M₁ × K⊗M₂ ≅ K⊗M` (`sumIso`, `prodBasis`).
   - The determinant functional `detFun b : K ⊗ ⋀^g M → K` is injective (hodge-lattice's steps
     2-4) and sends `1 ⊗ ∧w` to `1`.
   - So the three determinant lattices become `𝓞_K`-submodules `I₁, I₂, I ⊆ K` containing `1`,
     with equal indices (`secIndex_map`).
2. **`I = I₁ I₂`.**
   - `⊇`: a block determinant (`det_prodBasis_append`, from `Matrix.det_fromBlocks_zero₂₁`).
   - `⊆`: generalized Laplace expansion. Each `vₖ = j₁aₖ + j₂cₖ`.
     - `MultilinearMap.map_add_univ` expands `det` over subsets `T`.
     - If `#T ≠ g₁`, the family is dependent (a dimension count in `range jᵢ`), so the term is 0.
     - If `#T = g₁`, a permutation (`Finset.orderIsoOfFin`, `Equiv.sumCompl`) brings it to block
       form, at the cost of a sign.
3. **Indices.** `[I₁I₂ : 𝓞] = [I₁ : 𝓞][I₂ : 𝓞]` follows from the kernel's `secIndex_mul_absNorm`
   and the multiplicativity of `FractionalIdeal.absNorm` (`secIndex_one_mul`).

How `productHodgeLattice_of` is proved:
- `gᵢ = dim` comes from `Mᵢ.arch` and `dim_eq_of_isAnalyticUniformization`, and `CotangentRank`
  then gives `rank_L (L⊗cotᵢ) = gᵢ`.
- The kernel's `omegaLocal` gives `ωᵢ` finitely generated and spanning.
- The line property of `𝒢P` is `hodgeLattice_of_lattice` with
  `rank_L(L⊗cot_P) = g₁+g₂` (`rank_tensor_of_bijective`).
- `DetLatticeProd` yields the sections. They are lifted to germs through `toCotangent_surjective`
  and the compatibility clause of `ProductCotangent`.

## 4. What remains

- **`ProductCotangent`** (open, algebraic geometry at the generic unit and at the unit section).
  Mathlib has no computation of the stalk or the cotangent space of a fibre product of schemes.
  infra-stalks is building that infrastructure (`pullback_stalkGen`; maximal ideal and residue
  field of stalks of fibre products). Size estimate: medium to large (SPECULATIVE).
- **`TangentDimAtOrigin`** (open, shared with `HodgeLatticeTheorem`): dimension theory of
  varieties.
- Checked over `scratch/h-decomposition/Leaves.lean`'s own definitions: not done. product-unif
  did this for `productModelHeight_of_local` (9 min run). `Combined.lean` is checked against
  product-height's and the kernel's definitions, which product-unif showed agree with Leaves.lean.

## 5. Integration

- Suggested replacement of glue piece 5:
  `productModelHeight := ZInQ.UnifDims.productModelHeight_of_cotangent t.t35 hPC hT`.
  - `t.t35` is the existing textbook leaf T35.
  - `hT : TangentDimAtOrigin` is the hodge-lattice Prop, which `HodgeLatticeTheorem` also needs.
  - `hPC : ProductCotangent` is the new glue.
- `Torsion.lean` and `DetProd.lean` can become kernel modules unchanged. The rest needs
  product-unif's, product-height's and metrization2's pieces adopted first.

## 6. Reviews and unchecked

- One independent read-only model review (general-purpose agent) of `ProductCotangent`,
  `DetLatticeProd` and `productHodgeLattice_of`; verdict in §0 item 4. No human review.
- All locators (EGA IV, Stacks, Bourbaki, Mumford) are from memory: UNVERIFIED. Sizes are
  SPECULATIVE.
