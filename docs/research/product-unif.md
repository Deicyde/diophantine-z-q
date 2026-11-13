# product-unif: `ProductUnifSplits` (S-an) proved; `ProductMetrizationOfProductUnif` (S-alg) reduced

Status: research note (task product-unif, 2026-11-13).
- **Lean:** `scratch/product-unif/ProductUnif.lean`. It imports only the kernel module
  `ZInQKernel.HDecomp.Faltings.Height` and four Mathlib modules; there is no scratch import. It
  compiles with `lake env lean scratch/product-unif/ProductUnif.lean` in about 20 s. There is no
  `sorry` and no `axiom`. Every `#print axioms` lists only `propext`, `Classical.choice` and
  `Quot.sound` (VERIFIED, log).
- **Results log:** `scratch/product-unif/log.md`.
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = estimate or unchecked argument. **UNVERIFIED** =
locator from memory (no network).

## 0. Main result

The two targets are copied verbatim from `scratch/product-height/ProductHeight.lean` (§0 of the
Lean file, namespace `ZInQ.ProductHeight`, same full names, with everything they depend on). The
copy is checked against product-height's own definitions by `WithProductHeight.lean` (§5).

1. **`ProductUnifSplits` (S-an) is proved, with no hypotheses** (VERIFIED):

   ```lean
   theorem ZInQ.ProductUnif.productUnifSplits : ZInQ.ProductHeight.ProductUnifSplits
   ```

   The proof uses only Mathlib and the kernel's definitions (`GroupModel`, `evalAt`, `dom`,
   `IsAnalyticUniformization`). It follows product-height §2 (closed subgroups of `ℝⁿ`, the
   identity theorem, a Baire/measure argument), with one simplification: closedness of
   `ker(p₁ ∘ Φ)` is local. Near `0` that kernel is cut out by the regular functions of an affine
   open around the unit, so no closed-immersion argument for the unit section is needed (§1).

2. **`ProductMetrizationOfProductUnif` (S-alg) is reduced to the kernel's
   `HodgeLatticeTheorem`, metrization's two open glue Props, and one new glue Prop** (VERIFIED):

   ```lean
   theorem ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
       (hH  : ZInQ.DefFaltings.HodgeLatticeTheorem)        -- kernel glue (Models.lean); reduced by hodge-lattice
       (hD  : ZInQ.ProductUnif.ProductUnifDims)            -- NEW glue: dimensions in product form
       (hLS : ZInQ.Metrization.ProductLocalStructure)      -- metrization's glue (affine product charts)
       (hL  : ZInQ.Metrization.ProductHodgeLattice) :      -- metrization's glue (Hodge lattice of a product)
       ZInQ.ProductHeight.ProductMetrizationOfProductUnif
   ```

   - All the calculus in between is proved. Two pieces are ported unchanged from
     `scratch/metrization/` onto the kernel's types: `jacDetDescends` (the Jacobian
     determinant descends to the Hodge line) and `productJacobian` (the Jacobian of the product
     uniformization is block diagonal). Those copies compile without change, which confirms that
     metrization's def-faltings copy matches the kernel.
   - The covolume and height bookkeeping is proved: `covolume_of_cast`, plus product-height's
     `prodLattice_facts` and `modelHeight_add_of`.
   - The factor metrizations are built in the proof (`productMetrizationOfProductUnif_of`).

3. **Consequence for P2.** product-height proved
   `productModelHeight_of_splits : ProductUnifSplits → ProductMetrizationOfProductUnif → P2`.
   With item 1 this gives (VERIFIED, `WithProductHeight.lean`):

   ```lean
   theorem ZInQ.ProductUnif.productModelHeight_of_local (hH : HodgeLatticeTheorem)
       (hD : ProductUnifDims) (hLS : Metrization.ProductLocalStructure)
       (hL : Metrization.ProductHodgeLattice) : ZInQ.H5Neron.ProductModelHeight
   ```

   So glue piece 5 of `GluePieces` (P2) depends only on:
   - `HodgeLatticeTheorem`, shared with `MetrizationExists`;
   - metrization's `ProductLocalStructure` and `ProductHodgeLattice`, already named and shared
     with `ProductMetrizationGeo`;
   - the one new Prop `ProductUnifDims`.

   It needs no AN3 and no leaf.

4. **No statement is false, vacuous or inert.** Both targets are true as stated (product-height's
   review, and §2 here). An independent model review checked the new Props `ProductUnifDims`,
   `ProductHodgeAdd` and `ProductHodgeSections`: all three are true for every instance (including
   `g = 0` and an `e` incompatible with any generic-fibre product), none is vacuous, and none is a
   disguised form of S-alg. Its docstring corrections are applied (§6).

5. **One finding about the statement of S-alg (not a defect).** S-alg does not assume that
   `prodUnif ∘ cast` is an analytic uniformization of the product model. Its proof still needs the
   analytic clauses of `prodUnif`. These are true (product-height's `ProductUnifAnalytic`,
   metrization's `ProductUniformizationAnalytic`), so S-alg is still true. But they enter the
   reduction as an input, `ProductLocalStructure`. Supplying them is the job of S-an, in
   `productMetrizationSplit_of_splits`, where `prodUnif ∘ cast = Φ ∘ T`. A version of S-alg with
   that clause as an extra hypothesis would drop `ProductLocalStructure` from item 2.

## 1. Results (all VERIFIED: compiled, standard axioms only)

`ProductUnif.lean`, namespace `ZInQ.ProductUnif` unless marked.

| Lean name | statement |
|---|---|
| `rcore`, `ccore` | real / complex core `{v ∣ 𝕜v ⊆ H}` of an additive subgroup |
| `exists_isolated` | closed `H ⊂ E` (finite-dim real), `rcore H ⊓ W = ⊥` ⇒ points of `H ∩ W` uniformly isolated |
| `exists_countable_add` | a closed subgroup is `rcore H + S`, `S` countable |
| `rcore_sup_eq_top` | closed `H₁, H₂` with `H₁ + H₂ = E` ⇒ `rcore H₁ ⊔ rcore H₂ = ⊤` (`Measure.addHaar_submodule`) |
| `isClosed_of_local` | a subgroup cut out near `0` by functions continuous there is closed |
| `rcore_le_ccore` | if near `0` the subgroup is cut out by holomorphic functions, its real core is complex (identity theorem, `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) |
| `eq_zero_of_real_line_mem` | a discrete `ℤ`-lattice contains no real line |
| `pts_eq_of_evalAt` | two `τ`-points in an affine open `V` with equal `evalAt` on `Γ(V)` are equal (`IsAffineOpen.SpecMap_appLE_fromSpec`, `IsAffineOpen.fromSpec_top`) |
| `kerSub_facts` | the kernel of a holomorphic homomorphism `ℂ^g → 𝒢(ℂ)_τ` (clauses 1, 4, 5) is closed and its real core is complex |
| **`productUnifSplits`** | **`ZInQ.ProductHeight.ProductUnifSplits`** |
| `ProductUnifDims`, `ProductHodgeAdd`, `ProductHodgeSections` | new glue Props (§3) |
| `productMetrizationOfProductUnif_of` | `HodgeLatticeTheorem → ProductUnifDims → JacDetDescends → ProductHodgeAdd → S-alg` |
| `covolume_of_cast`, `productHodgeAdd_of` | `ProductHodgeSections → ProductHodgeAdd` (covolumes multiply; `modelHeight_add_of`) |
| `jacDetDescends'` | my `JacDetDescends` (with `dim A = d`) from metrization's `jacDetDescends` |
| `prodUnif_eq_prodPts`, `prodLattice_eq_metrization` | product-height's `prodUnif`, `prodLattice` are metrization's `prodPts`, `prodLattice` |
| `productHodgeSections_of` | `Metrization.ProductUniformizationAnalytic → Metrization.ProductHodgeLattice → ProductHodgeSections` |
| `productMetrizationOfProductUnif_of''`, `_of_metrization`, **`_of_local`** | S-alg from `HodgeLatticeTheorem`, `ProductUnifDims` and (`ProductHodgeSections` / metrization's `ProductUniformizationAnalytic`+`ProductHodgeLattice` / **`ProductLocalStructure`+`ProductHodgeLattice`**) |
| `ZInQ.Metrization.jacDetDescends`, `productJacobian`, `productUniformizationAnalytic_of` (§3b) | metrization's proofs, copied verbatim, compiled on the kernel's types |

`WithProductHeight.lean`: `productModelHeight_of_salg`, `_salg'`, `_salg''`, `_local`, which
prove `ZInQ.H5Neron.ProductModelHeight` from the reductions above, over product-height's own file.

Side files: `Analysis.lean` (§1 analysis, Mathlib only), `JacDet.lean`, `ProdJac.lean` (the
metrization ports, generated by `mk_prodjac.py`). Each compiles on its own.

## 2. How `ProductUnifSplits` is proved (Lean §1-§3)

Setting. `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` has homomorphic components. `Φ : ℂ^g → 𝒢P(ℂ)_τ` is an analytic
uniformization whose kernel is a full discrete lattice `Λ`. Put `ψᵢ = pᵢ ∘ Φ` (through `ptsEquiv`)
and `Kᵢ = ker ψᵢ` (`kerSub`).

1. **`Kᵢ` is closed and `rcore Kᵢ ≤ ccore Kᵢ`** (`kerSub_facts`).
   - Take an affine open `V` containing the image of `1` (`exists_isAffineOpen_mem_and_subset`;
     `Spec ℂ` has one point).
   - On the open set `N = dom ψᵢ V` (clause 4, via product-height's `proj_analyticClauses` and
     `analyticClauses_comp`): `z ∈ Kᵢ` iff `evalAt (ψᵢ z) V s = evalAt 1 V s` for all `s ∈ Γ(V)`
     (`pts_eq_of_evalAt`).
   - These functions are holomorphic on `N` (clause 5), so `isClosed_of_local` and
     `rcore_le_ccore` apply.
2. **`rcore K₁ ⊔ rcore K₂ = ⊤`.** `K₁ + K₂ = ℂ^g` by surjectivity, then `rcore_sup_eq_top`. The
   proof: by the isolation lemma, a closed subgroup is its real core plus a countable set. If the
   sum `P` of the cores were proper, `ℂ^g` would be a countable union of translates of the Haar-null
   `P`.
3. Put `V₁ = ccore K₂` and `V₂ = ccore K₁` (complex subspaces).
   - `V₁ ⊔ V₂ = ⊤` by steps 1 and 2.
   - `V₁ ⊓ V₂ = ⊥`, since `V₁ ∩ V₂ ⊆ K₁ ∩ K₂ = Λ` and `Λ` contains no real line.
   - `gᵢ = finrank Vᵢ`, so `g₁ + g₂ = g`.
4. Bases give `ιᵢ : ℂ^{gᵢ} ≅ Vᵢ ⊂ ℂ^g`.
   - Put `Φ₁ = ψ₁ ∘ ι₁`, `Φ₂ = ψ₂ ∘ ι₂` and `Λᵢ = ιᵢ⁻¹Λ`.
   - `T = cast ≫ split ≫ (ι₁ × ι₂) ≫ (V₁ × V₂ ≅ ℂ^g)` (`Submodule.prodEquivOfIsCompl`).
   - Hom, kernel and surjectivity follow from `ψ₂ ∘ ι₁ = 1` and `ψ₁ ∘ ι₂ = 1`.
   - Clauses 4 and 5 come from product-height's `proj_analyticClauses` and
     `analyticClauses_precomp`.
   - `Λᵢ` is discrete (`ZLattice.comap_discreteTopology`) and full: project `span_ℝ Λ = ⊤` along
     `πᵢ`, using `πᵢ Λ ⊆ Λᵢ`.
   - `Φ ∘ T = prodUnif e Φ₁ Φ₂ ∘ cast`.

## 3. The Props: leaf or glue, and status

| name | kind | statement (short) | status |
|---|---|---|---|
| `ProductHeight.ProductUnifSplits` (S-an) | glue (target) | a full-lattice uniformization of `𝒢P(ℂ)_τ` is `Φ₁ × Φ₂` after `T ∈ GL_g(ℂ)` | **proved** |
| `ProductHeight.ProductMetrizationOfProductUnif` (S-alg) | glue (target) | a product-form metrization of `𝒢P` yields metrizations of the factors with `h(M₁)+h(M₂) ≤ h(MP)` | **reduced** (item 2) |
| `DefFaltings.HodgeLatticeTheorem` | glue (kernel, `Models.lean`) | `hodgeSpace (dim A)` is an `L`-line and `⋀ω_𝒢` a full lattice in it | reduced by hodge-lattice (not a target here) |
| `ProductUnif.ProductUnifDims` (S-alg-1) | **new glue** (algebra + calculus) | in product form at `τ`: `dim A = g₁`, `dim B = g₂`, factor Jacobians nonsingular | open. Why true: `finrank_eq_one` gives `g ∈ {0, n₁+n₂}`; `cot_P = cot₁ ⊕ cot₂`; block Jacobian; `g = 0` by triviality of points (docstring; reviewed) |
| `ProductUnif.JacDetDescends` (S-alg-2) | glue | `jacDet Φ` is the value on wedges of a `τ`-semilinear map | **proved** (`jacDetDescends'`, from metrization) |
| `ProductUnif.ProductHodgeAdd` (S-alg-3) | glue | factor Hodge data given, MP in product form ⇒ `h(D₁)+h(D₂) ≤ h(MP)` | **reduced** to `ProductHodgeSections` |
| `ProductUnif.ProductHodgeSections` (S-alg-3a) | glue | nonzero sections with multiplicative index and coefficients | **reduced** to metrization's `ProductUniformizationAnalytic` + `ProductHodgeLattice` |
| `Metrization.ProductUniformizationAnalytic` | glue (metrization) | analytic clauses of `prodPts` | reduced by metrization to `ProductLocalStructure` (proof ported here) |
| `Metrization.ProductLocalStructure` | glue (metrization; algebraic geometry at complex points) | membership in an open and regular functions near a point of `𝒢₁ × 𝒢₂` are sums of products from the factors | open (affine charts `Spec(R₁ ⊗ R₂)`, basic opens; STANDARD) |
| `Metrization.ProductHodgeLattice` | glue (metrization; algebra) | `⋀^{g₁+g₂}ω_{𝒢P} ∋ (a₁a₂)·d(p₁*f₁, p₂*f₂)` with multiplicative index | open (`ω_P = p₁*ω₁ ⊕ p₂*ω₂`; STANDARD) |

No leaf is introduced. The decomposition gains exactly one new named glue Prop,
`ProductUnifDims`. Everything else S-alg needs is glue already named by def-faltings (kernel) and
metrization.

## 4. What remains (SPECULATIVE sizes)

- **`ProductUnifDims`** (medium). It needs:
  - the cotangent space at the unit of a fibre product of group models
    (`cot_P = cot₁ ⊕ cot₂`; the same input as `ProductHodgeLattice`);
  - `finrank (L ⊗ ⋀^g C) = C(n, g)` (metrization's `ExtLine.lean`, `eq_of_finrank_one`, proves
    the key case);
  - `n = dim A` (hodge-lattice's `TangentDimAtOrigin`);
  - the block-Jacobian rank argument (metrization's `productJacobian` covers pulled-back germs;
    general germs need the class argument);
  - for `g = 0`, that a positive-dimensional abelian variety has more than one complex point.

  A natural split is into a dimension half and a nonsingularity half. Not done.
- `ProductLocalStructure` and `ProductHodgeLattice`: see `docs/research/metrization.md` §3-§4.

## 5. Integration

- `scratch/product-unif/WithProductHeight.lean` is generated by `build_with_product_height.py`.
  It is product-height's `ProductHeight.lean` (verbatim, with its own definitions, importing
  `H5Neron`), followed by §1-§4 of `ProductUnif.lean` without my §0 copy, followed by the
  composite theorems. It compiles: 0 errors, standard axioms (VERIFIED). So my
  `productUnifSplits` and reductions are about product-height's Props themselves.
- **Leaves.lean.** `build_integrated.sh` writes `LeavesIntegrated.lean`. It consists of
  `scratch/h-decomposition/Leaves.lean`, product-height's §1-§6 and my §1-§4 (all without
  `open PkgI3 (AbVar)`), and `productModelHeight_of_local`, which closes Leaves.lean's
  `ZInQ.H5Neron.ProductModelHeight`, the type of `GluePieces.productModelHeight`. Result: see the log
  (LEAVES-RESULT). The generated file is not committed.
- Suggested replacement of glue piece 5:
  `productModelHeight := ZInQ.ProductUnif.productModelHeight_of_local hH hD hLS hL`.
  - `hH`: `HodgeLatticeTheorem`.
  - `hD`: `ProductUnifDims`.
  - `hLS`, `hL`: metrization's two Props.
- The file can become a kernel module unchanged (minus the §0 copy) once product-height's and
  metrization's pieces are adopted.

## 6. Reviews and unchecked

- One independent read-only model review (general-purpose agent) of `ProductUnifDims`,
  `ProductHodgeAdd` and `ProductHodgeSections` as formalized.
  - Verdict: all three TRUE for every instance, not vacuous, not disguised forms of S-alg.
  - It noted that the analytic clauses of `prodUnif ∘ cast` are a real ingredient (true, but not
    among the hypotheses).
  - Its docstring corrections are applied:
    - "wedges span `hodgeSpace`";
    - `nᵢ = dim A` by base-change invariance of dimension;
    - `gᵢ = dim` first;
    - "any nonzero `sᵢ`" instead of "bases `sᵢ`" (`⋀ω` need not be free).
  - It did not review the metrization ports, which are compiled proofs.
- The S-an proof is compiled; no review was needed for correctness. Its statement was reviewed
  twice by product-height.
- The locators (EGA IV 4.1.4, Bourbaki) are from memory: UNVERIFIED. The sizes in §4 are
  SPECULATIVE. No human review.
