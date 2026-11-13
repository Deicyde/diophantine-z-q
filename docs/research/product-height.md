# product-height: the glue Prop `ProductModelHeight` (P2)

Status: research note (task product-height, 2026-11-13).
- **Lean:** `scratch/product-height/ProductHeight.lean`. It imports only the kernel module
  `ZInQKernel.HDecomp.Faltings.H5Neron` (no scratch import). It compiles with
  `lake env lean scratch/product-height/ProductHeight.lean` in about 1 min. There is no `sorry`
  and no `axiom`, and all 23 `#print axioms` list only `propext`, `Classical.choice` and
  `Quot.sound` (VERIFIED, log).
- **Results log:** `scratch/product-height/log.md`.
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = estimate or unchecked argument. **UNVERIFIED** =
locator from memory (no network).

## 0. Verdict

The target is `ZInQ.H5Neron.ProductModelHeight` (P2): `h(𝒢₁) + h(𝒢₂) ≤ h(𝒢P)` for every product
`𝒢P ≅ 𝒢₁ × 𝒢₂` of smooth group models (`IsProductModel`). Its text is the same in the kernel
(`ZInQKernel/HDecomp/Faltings/H5Neron.lean`), in `scratch/h5-neron/` and in `scratch/h5-glue/`
(VERIFIED). The verbatim copy in §0 of the Lean file is checked against the kernel Prop by
`copy_iff : Copy.ProductModelHeight ↔ H5Neron.ProductModelHeight := Iff.rfl` (VERIFIED).

1. **P2 is true and not vacuous** (STANDARD; equality holds).
2. **No AN3-type input is needed.** The claim of h5-glue §4 is refuted: there, both halves of
   AN3 (existence and uniqueness of analytic uniformizations) were said to enter. P2 is proved
   from two glue Props, neither of which involves AN3:

   ```lean
   theorem ZInQ.ProductHeight.productModelHeight_of_splits
       (hS : ProductUnifSplits)                    -- glue S-an: elementary analysis
       (hA : ProductMetrizationOfProductUnif) :    -- glue S-alg: Hodge theory of a product
       ZInQ.H5Neron.ProductModelHeight
   ```

   VERIFIED, compiled, standard axioms only.
   - **S-an** (`ProductUnifSplits`) splits the product's own uniformization `Φ` of
     `𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` (full discrete kernel) as `Φ ∘ T = Φ₁ × Φ₂`, `T` linear. The proof uses
     only:
     - the structure of closed subgroups of `ℝⁿ`;
     - the identity theorem in one variable;
     - Baire's theorem;
     - the clauses of `IsAnalyticUniformization` (§2).

     No uniformization theorem and no comparison of two uniformizations is used.
   - **S-alg** (`ProductMetrizationOfProductUnif`) builds metrizations of the factors from a
     product-form metrization of the product. It is Hodge theory and algebra with the
     uniformizations given: the mirror image of g0-heightadd's `ProductMetrizationGeo`.
   - The change of coordinates `Φ ↦ Φ ∘ T_τ` between the two is proved (`recoordM`,
     `recoordM_modelHeight`, `isAnalyticUniformization_comp`).
3. **h5-glue's "a product uniformization must split" is right as a step, but the step is
   elementary.** It is S-an. It restricts the given `Φ` to the identity components of
   `ker(p₂ ∘ Φ)` and `ker(p₁ ∘ Φ)`, which are complementary complex subspaces. It is not AN3.
4. **Correction inside this task.** The first draft of this note (commit 20550ab1) claimed the
   opposite, that AN3-type input is needed. An independent model review refuted it. I re-checked
   every step (§2, log) and changed the verdict. The forcing lemmas (§1 table; Lean §4) stay true theorems
   (P2 forces uniformizations of the factors from one of the product), but they are no evidence
   of AN3 strength: S-an provides that descent elementarily.
5. **New proved pieces** (VERIFIED):
   - the product lattice `Λ₁ × Λ₂` is a full discrete lattice with
     `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂` (`prodLattice_facts`, Lean §5b; Mathlib measure theory). This
     is the covolume clause needed by S-alg and by `ProductMetrizationGeo`;
   - `ptsEquiv` (complex points of a product are the product of the complex points, as groups);
   - `prodUnif_clauses` (the algebraic clauses of the product uniformization);
   - `recoordM` (change of linear coordinates of a metrized model; the height is unchanged);
   - `proj_analyticClauses` (the analytic clauses of the factor maps `p₁ ∘ Φ ∘ ℓ` in S-an).
6. **Route U** (g0-heightadd's reduction, now on the kernel's types) is also compiled:
   `productModelHeight_of_geo : U → MetrizationDimUnique → MetrizationExists →
   ProductMetrizationGeo → P2`. It uses AN3 (U, and existence inside `MetrizationExists`), so the
   recommended route is the AN3-free one of item 2.

## 1. Results (all VERIFIED: compiled, standard axioms only)

| Lean name (`ZInQ.ProductHeight.`) | statement |
|---|---|
| `copy_iff` | the verbatim copy of P2 (from `scratch/h5-neron/H5Neron.lean`) is the kernel Prop (`Iff.rfl`) |
| **`productModelHeight_of_splits`** | **`ProductUnifSplits → ProductMetrizationOfProductUnif → P2`** |
| `productMetrizationSplit_of_splits` | `ProductUnifSplits → ProductMetrizationOfProductUnif → ProductMetrizationSplit` |
| `productModelHeight_of_split` | `ProductMetrizationSplit → P2` |
| `isAnalyticUniformization_comp` | `Φ` an analytic uniformization with kernel `Λ` ⇒ `Φ ∘ T` one with kernel `T⁻¹Λ` (`T ∈ GL_g(ℂ)`) |
| `recoordM`, `recoordM_model`, `recoordM_modelHeight` | change of linear coordinates of a metrized model: same group model, same height (from def-faltings' `HodgeData.recoord`, `GroupModel.jacDet_comp`, `HodgeData.modelHeight_recoord`) |
| `ptsProj_bijective`, `ptsEquiv` | `𝒢P(ℂ)_τ ≃* 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` for `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` with homomorphic components |
| `prodUnif_clauses` | `z ↦ (Φ₁ z₁, Φ₂ z₂)` (coordinates `Fin.append`) is a homomorphism, onto, with kernel exactly `prodLattice Λ₁ Λ₂` |
| `prodUnif_isAnalyticUniformization` | with glue `ProductUnifAnalytic`, `Φ₁ × Φ₂` is an analytic uniformization of the product |
| `proj_comp_unif` | `p₁ ∘ Φ` is a surjective homomorphism onto `𝒢₁(ℂ)_τ` |
| `covolume_prod`, `isAddFundamentalDomain_prod`, `instIsZLatticeProd`, `discreteTopology_prod` | for full lattices `Λᵢ ⊂ Eᵢ` and Haar measures, `Λ₁ × Λ₂ ⊂ E₁ × E₂` is a full lattice and `covol(Λ₁ × Λ₂, μ₁ × μ₂) = covol Λ₁ · covol Λ₂` (§5b; also standalone in `Lattice.lean`, Mathlib only) |
| `splitCL_measurePreserving`, `prodLattice_eq_comap`, `prodLattice_facts` | `prodLattice Λ₁ Λ₂ ⊂ ℂ^{g₁+g₂}` is a full discrete lattice with `covol = covol Λ₁ · covol Λ₂` |
| `prodUnif_fullLattice` | with `ProductUnifAnalytic`: a product of full-lattice uniformizations is one, with multiplicative covolume |
| `evalAt_comp`, `dom_comp`, `analyticClauses_comp`, `analyticClauses_precomp`, `proj_analyticClauses` | clauses 4 and 5 of `IsAnalyticUniformization` transport along morphisms of `𝓞_L`-schemes and along `ℂ`-linear maps; in particular `z ↦ p₁(Φ(ℓ z))` satisfies them for `𝒢₁` (the "clauses restrict" step of S-an, Lean §6b) |
| `le_of_productModelHeight` | P2 bounds every metrization of the product below |
| `metrizable_left/right_of_productModelHeight`, `analyticUnif_left_of_productModelHeight` | P2, a metrization of the product and `h(other factor) ≠ ⊥` give a metrization, hence a full-lattice uniformization, of the factor |
| `metrizationHeightUnique_of` | `U → MetrizationDimUnique → MetrizationHeightUnique` |
| `productModelHeight_of_unique`, `productModelHeight_of`, `productModelHeight_of_geo` | route U |
| `productMetrizationSplit_of` | route U's inputs imply `ProductMetrizationSplit` |

Copied from g0-heightadd (`scratch/g0-heightadd/part_heightadd.lean`, `part_prod.lean`, where they
are stated over the def-faltings copy `Prefix.lean`): `ProductMetrization`, `MetrizationExists`,
`MetrizationDimUnique`, `ProductMetrizationGeo`, `modelHeight_add_of` and
`productMetrization_of_geo`. Their statements are unchanged; here they are over the kernel's
`PkgI3.AbVar`, `DefFaltings.GroupModel` and `H5Neron.IsProductModel`.

## 2. Why `ProductUnifSplits` holds without AN3

This is an argument, not Lean. It was found by the model review and re-checked step by step by
the author; each ingredient is STANDARD.

**Setting.** `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` has homomorphic components, so `𝒢P(ℂ)_τ ≅ 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ`
(`ptsEquiv`, proved). `Φ : ℂ^g → 𝒢P(ℂ)_τ` is an analytic uniformization whose kernel is a full
discrete lattice `Λ`. Put `Kᵢ = ker(pᵢ ∘ Φ)`.

1. **`K₁` is closed.** `𝒢₁` is separated, so its unit section is a closed immersion. A
   `τ`-point `y` of `𝒢₁` equals `1` iff its image lies in that closed set, because a morphism
   `Spec ℂ → Spec 𝓞_L` over `τ` is unique. So `{z | p₁Φ(z) ≠ 1}` is `dom Φ U` for a Zariski open
   `U` of `𝒢P`, which is open by clause 4.
2. **The identity component `W₂` of `K₁` is a complex subspace.** A closed subgroup of `ℝ^{2g}`
   is a real subspace plus a discrete group (Bourbaki, *Topologie générale* VII §1, UNVERIFIED).
   For `w ∈ W₂` and `f` regular near `1` on `𝒢₁`, the map `t ↦ f(p₁Φ(tw))` is holomorphic near
   `0`, by clause 5 applied to `p₁*f` on `p₁⁻¹V`. It is constant for real `t`, so it is constant
   near `0`. A `τ`-point of an affine open is determined by the values of its functions, so
   `tw ∈ K₁` for small complex `t`. Hence `ℂw ⊆ W₂`. Define `W₁ ⊆ K₂` likewise.
3. **`ℂ^g = W₁ ⊕ W₂`.**
   - By surjectivity, `K₁ + K₂ = ℂ^g`: `Λ ⊆ K₁ ∩ K₂`.
   - Each `Kᵢ` is a countable union of translates of its identity component, so by Baire (or
     measure) `W₁ + W₂ = ℂ^g`.
   - `W₁ ∩ W₂ ⊆ K₁ ∩ K₂ = Λ` is a discrete subspace, hence `0`.
4. **The factor uniformizations.** Put `Φ₁ = p₁ ∘ Φ|_{W₁}`.
   - It is onto, because `p₁Φ(W₂) = 1`.
   - Its kernel is `W₁ ∩ K₁ ⊆ K₁ ∩ K₂ = Λ`, i.e. `Λ ∩ W₁`.
   - `Λ = (Λ ∩ W₁) ⊕ (Λ ∩ W₂)`: for `λ = w₁ + w₂`, `Φ(λ) = 1` forces `p₁Φ(w₁) = 1`. So both
     parts are full lattices.
   - Clauses 4 and 5 restrict to `Wᵢ`, using `evalAt` compatibility with `pᵢ`.
   - With `T : ℂ^{g₁} × ℂ^{g₂} ≅ W₁ ⊕ W₂`, `Φ(T(z₁, z₂)) = (Φ₁ z₁, Φ₂ z₂)`.

None of this needs `g = dim`, a uniformization theorem, or the comparison of two
uniformizations.

**Why S-alg holds** (STANDARD; mirror image of `ProductMetrizationGeo`).
- `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}`, and `⋀^{top}` splits as a tensor product.
- The Jacobian of `Φ₁ × Φ₂` at `0` on `p₁*f ∧ p₂*h` is block diagonal. Since `coeff ≠ 0` on that
  nonzero wedge, both blocks are square, so `gᵢ(τ) = dim 𝒢ᵢ`. In the case `g = 0` everything is
  trivial and the heights are `0`.
- `jacDet Φᵢ` descends to a semilinear map on `⋀^{gᵢ}`, because derivatives at `0` kill `𝔪²`.
- Indices, coefficients and covolumes multiply (`modelHeight_add_of`), so equality holds.

## 3. The Props: leaf or glue, and why each is true

| name | kind | statement | status |
|---|---|---|---|
| `H5Neron.ProductModelHeight` (P2) | glue (target) | `h(𝒢₁) + h(𝒢₂) ≤ h(𝒢P)` (equality holds; Faltings 1983 §1, Deligne Sém. Bourbaki 616 §1, UNVERIFIED) | **reduced** to S-an + S-alg |
| `ProductUnifSplits` (S-an, new) | glue, elementary analysis | a full-lattice uniformization of `𝒢P(ℂ)_τ` is `Φ₁ × Φ₂` after `T ∈ GL_g(ℂ)` | unproved; §2 |
| `ProductMetrizationOfProductUnif` (S-alg, new) | glue, Hodge theory | a product-form metrization of `𝒢P` yields metrizations `M₁`, `M₂` with `h(M₁)+h(M₂) ≤ h(MP)` | unproved; §2 |
| `ProductUnifAnalytic` (new) | glue, no AN3 | analytic clauses for `Φ₁ × Φ₂` (a sub-step of route U's `ProductMetrizationGeo`; not used by the main route). Basic opens `D(Σ aᵢ ⊗ bᵢ)` of affine products form a basis; products of opens do not (EGA I 3.2.2 / Stacks 01JR, UNVERIFIED) | unproved |
| `ProductMetrizationSplit` (S) | glue | P2 with attained infima. It is close to a restatement of P2 and is kept only as the hinge between S-an/S-alg and P2 | reduced to S-an + S-alg |
| `MetrizationHeightUnique` (new), `AnalyticUniformizationUnique` (U), `MetrizationDimUnique`, `MetrizationExists`, `ProductMetrization`, `ProductMetrizationGeo` | glue (route U) | as in g0-heightadd; U and existence are AN3 | route U only; not needed for P2 |

No new literature leaf is introduced.

## 4. What remains (SPECULATIVE sizes)

- **S-an** (`ProductUnifSplits`), medium. It needs:
  - closed subgroups of `ℝⁿ` (not found in Mathlib v4.35; not searched exhaustively);
  - the identity theorem (in Mathlib: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`,
    `Mathlib/Analysis/Analytic/Uniqueness.lean`, VERIFIED by reading);
  - Baire;
  - the Zariski-closedness of `p₁ x = 1`.

  The "clauses 4 and 5 restrict" step is **done**: `proj_analyticClauses` (Lean §6b, VERIFIED).
- **S-alg** (`ProductMetrizationOfProductUnif`), large. It needs the stalk and cotangent space of
  a fibre product at the unit (`ω_{𝒢P} = ω₁ ⊕ ω₂`), `HodgeLatticeTheorem` for the factors,
  `⋀^{top}` of a direct sum, multiplicativity of `secIndex`, the block Jacobian, and the descent
  of `jacDet` to `⋀^g`. The covolume of `Λ₁ × Λ₂` is **done**: `prodLattice_facts` (Lean
  §5b, VERIFIED). Constancy of `gᵢ(τ)` in `τ` and the `Fin.cast` reindexing are part of S-alg.

## 5. Integration

- The file imports only `ZInQKernel.HDecomp.Faltings.H5Neron`. It can become a kernel module
  (`ZInQKernel/HDecomp/Faltings/ProductHeight.lean`) unchanged, minus the §0 copy.
- In `scratch/h-decomposition/Leaves.lean`, `GluePieces.productModelHeight` has type
  `ZInQ.H5Neron.ProductModelHeight`. That is the Leaves.lean copy, over Leaves.lean's
  `DefFaltings.AbVar`. **Integration check (VERIFIED):** `scratch/product-height/build_integrated.sh`
  appends §1-§6 to a copy of `Leaves.lean`, with the §0 copy and `open PkgI3 (AbVar)` dropped,
  together with
  `example (hS : ProductUnifSplits) (hA : ProductMetrizationOfProductUnif) :
  ZInQ.H5Neron.ProductModelHeight := productModelHeight_of_splits hS hA`.
  - `lake env lean` on the result gives 0 errors (last run on the final file, with Lean §5b
    and §6b: 8.9 min).
  - `productModelHeight_of_splits` and `productModelHeight_of_geo` use only the standard axioms
    there.
  - The generated file is not committed (log).
- Suggested replacement of glue piece 5: `productModelHeight := productModelHeight_of_splits hS hA`,
  with the two new glue Props `hS : ProductUnifSplits` and `hA : ProductMetrizationOfProductUnif`.
- h-decomposition's remark that P2 "needs AN3" (from h5-glue §4) should be dropped.

## 6. Reviews and unchecked

- One read-only model review (general-purpose agent) of the first version. Findings:
  - all Props true;
  - the `ProductUnifAnalytic` docstring correct;
  - `ProductMetrizationSplit` close to a restatement of P2;
  - **the AN3-necessity claim unsound** (the argument of §2).

  Acted on: §6 added and the verdict changed.
- A second pass of the same reviewer covered §6.
  - Both new glue Props are true exactly as formalized, for every `g` including `g = 0`.
  - Neither is vacuous, and neither hides AN3.
  - `gᵢ(τ) = dim 𝒢ᵢ` is derivable inside S-alg, from `finrank_eq_one` and the block Jacobian.
  - The nonzero-wedge fact is algebraic.
  - Its wording nits were applied.
- Locators (Bourbaki, Mumford, Faltings 1983, Deligne 616, EGA, Stacks) are from memory:
  UNVERIFIED.
- §2 is an argument, not Lean.
- The sizes in §4 are SPECULATIVE. No human review.
