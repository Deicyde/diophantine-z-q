# product-height: `ZInQ.H5Neron.ProductModelHeight` (P2)

**Verdict.** P2 is true and not vacuous. **It does not need AN3-type input.** h5-glue's claim
that both halves of AN3 (existence and uniqueness of analytic uniformizations) enter is refuted.
P2 is proved in Lean from two new glue Props, neither involving AN3:

- `ProductUnifSplits` (S-an). The product's *own* uniformization `Φ` (full discrete kernel)
  splits as `Φ ∘ T = Φ₁ × Φ₂`. The proof restricts `Φ` to the identity components of
  `ker(p₂∘Φ)` and `ker(p₁∘Φ)`, which are complementary complex subspaces. It uses closed subgroups
  of `ℝⁿ`, the identity theorem and Baire: elementary, no comparison of uniformizations.
- `ProductMetrizationOfProductUnif` (S-alg). This is Hodge theory of a product with the
  uniformizations given (mirror image of g0-heightadd's `ProductMetrizationGeo`).

Main theorem: `ZInQ.ProductHeight.productModelHeight_of_splits hS hA : ProductModelHeight`.
h5-glue's "a product uniformization must split" is right as a step (S-an), but the step is
elementary.

My first draft claimed AN3 was needed. An independent model review refuted it; I re-checked each
step and corrected the verdict. A second review pass confirmed that both new Props are true as
formalized.

**What compiles** (`scratch/product-height/ProductHeight.lean`, imports only
`ZInQKernel.HDecomp.Faltings.H5Neron`; ~1 min; 21/21 `#print axioms` standard; no sorry or axiom):
- `copy_iff`: the verbatim copy of P2 is the kernel Prop (`Iff.rfl`).
- `productModelHeight_of_splits`, `productMetrizationSplit_of_splits`,
  `productModelHeight_of_split`.
- `recoordM` / `recoordM_modelHeight` / `isAnalyticUniformization_comp`: change of linear
  coordinates of a metrized model, height unchanged.
- `ptsEquiv`: `𝒢P(ℂ)_τ ≃* 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ`.
- `prodUnif_clauses`: the algebraic clauses of the product uniformization, with kernel
  `Λ₁ × Λ₂`; the analytic clauses are glue `ProductUnifAnalytic`.
- `prodLattice_facts` / `covolume_prod`: `Λ₁ × Λ₂` is a full discrete lattice with
  `covol = covol Λ₁ · covol Λ₂` (Mathlib measure theory; also standalone in `Lattice.lean`).
- Route U (g0-heightadd's reduction, ported to the kernel's types; uses AN3):
  `productModelHeight_of_geo`, `productModelHeight_of_unique` with the new
  `MetrizationHeightUnique`.
- Forcing lemmas: `le_of_productModelHeight`, `metrizable_left/right_…`,
  `analyticUnif_left_…`.
- **Integration check:** the file was pasted into a copy of `scratch/h-decomposition/Leaves.lean`,
  with an `example` closing its `GluePieces.productModelHeight` type from the two glue Props.
  Result: 0 errors (8.2 min on the final file), standard axioms (`build_integrated.sh`).

**What remains.** S-an and S-alg are unproved (sizes SPECULATIVE):
- S-an, medium: closed subgroups of `ℝⁿ`, `evalAt` along projections.
- S-alg, large: `ω_{𝒢P} = ω₁ ⊕ ω₂` (stalk of a fibre product), the factors' Hodge lattices, the
  descent of `jacDet` to `⋀^g`, multiplicativity of the index. The covolume part is proved.

The §2 splitting argument is not in Lean; locators are UNVERIFIED; no human review.
Report: `docs/research/product-height.md`. Log: `scratch/product-height/log.md`.
