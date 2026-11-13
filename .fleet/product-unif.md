# product-unif (fleet summary)

**Verdict.** `ProductUnifSplits` (S-an) is **proved outright** (no hypotheses). `ProductMetrizationOfProductUnif`
(S-alg) is **reduced** to the kernel's `HodgeLatticeTheorem`, metrization's two open glue Props
`ProductLocalStructure` and `ProductHodgeLattice`, and one new glue Prop, `ProductUnifDims`. Neither target is
false, vacuous or inert.

**What compiles** (`scratch/product-unif/`, all standard axioms, no sorry):
- `ProductUnif.lean`: imports only `ZInQKernel.HDecomp.Faltings.Height` plus Mathlib; about 20 s.
  - `ZInQ.ProductUnif.productUnifSplits : ZInQ.ProductHeight.ProductUnifSplits`. The ingredients:
    - closed subgroups of ℝⁿ (real core + countable set);
    - a Haar-null argument for `rcore K₁ ⊔ rcore K₂ = ⊤`;
    - the identity theorem (the real core is complex);
    - `pts_eq_of_evalAt`: complex points in an affine open are separated by regular functions.
      With it, `ker(pᵢ∘Φ)` is locally cut out by holomorphic functions, so closed.
  - `productMetrizationOfProductUnif_of_local : HodgeLatticeTheorem → ProductUnifDims →
    Metrization.ProductLocalStructure → Metrization.ProductHodgeLattice → S-alg`. On the way:
    - `JacDetDescends` is proved: metrization's proof, ported unchanged to the kernel's types;
    - `productJacobian` is ported;
    - `ProductHodgeAdd` is reduced to `ProductHodgeSections`, then to metrization's Props;
    - `productUnifDims_of : ProductUnifDimsEq → Metrization.JacDetNondegenerate → ProductUnifDims` (alternative).
- `WithProductHeight.lean`: product-height's own file plus mine. It proves
  `ZInQ.H5Neron.ProductModelHeight` (P2) from the same four Props, and product-height's
  `ProductUnifAnalytic` from `ProductLocalStructure`. This checks that the Props are product-height's.
- Leaves.lean integration (`build_integrated.sh`): Leaves.lean + product-height + mine, with
  `productModelHeight_of_local` closing `GluePieces.productModelHeight`'s type. 0 errors, 9 min, standard axioms.

**Review.** An independent model review found `ProductUnifDims`, `ProductHodgeAdd` and
`ProductHodgeSections` true, non-vacuous and not disguised conclusions; its docstring fixes are applied.
Finding: S-alg's hypotheses omit the analytic clauses of `prodUnif ∘ cast`. They are true, but the
reduction needs them, which is why `ProductLocalStructure` is an input.

**What remains.** `ProductUnifDims` (new glue: product-form dimensions `gᵢ = dim` and nonsingular
factor Jacobians, via cotangent splitting and the block Jacobian), plus the existing glue
`HodgeLatticeTheorem`, `ProductLocalStructure` and `ProductHodgeLattice`. Report:
`docs/research/product-unif.md`.
