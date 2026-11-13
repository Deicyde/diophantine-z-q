# g0-product (G17, `ProductExists`) — fleet note

**Result: `G0Split.ProductExists` is proved in Lean with no hypotheses** (`G0Product.productExists`,
axioms propext / Classical.choice / Quot.sound, VERIFIED). The statement and its dependencies
(`PkgI3.AbVar`, `ZInQ.DefFaltings.AbVar`, their `dim`, `G0Split.IsProductOf`) are verbatim copies
from `scratch/g0-split/Split.lean`; the proof uses Mathlib v4.35.0 only: no leaf, no project glue.
The piece is true and non-vacuous (`P` is the fibre product `A ×_L Z`).

What compiles (`lake env lean scratch/g0-product/Product.lean`, ~6 s):
- `geometricallyIntegral_comp`, `prodAbVar` (`A.X ⊗ Z.X` is a proper smooth geometrically
  integral group scheme), `isProductOf_prodAbVar` (projections, `lift fst snd = 𝟙`);
- `DimProductOverField` (dim of a product of finite-type schemes over a field) from
  `DimTensorFG` (dim of `R ⊗_K S` for f.g. algebras) via affine covers;
- `DimTensorFG` itself, from Mathlib's Noether normalization plus two lemmas proved here:
  Krull dimension is invariant under injective integral maps (incomparability + going up) and
  tensor products of integral maps are integral.
- Integration check: `scratch/g0-product/mkcheck.sh` appends the proof to Split.lean and proves
  `HSyn.glueOutputs_of_leaves_g0product` (= `glueOutputs_of_leaves` with
  `hProdE := G0Product.productExists`); compiled, standard axioms (2m54s).

What remains: nothing for this piece. Integration: move §2-§5 of `Product.lean` into
`part_split.lean` (names `HSyn.G0Split.…`) or a Mathlib-only module under `ZInQKernel/HDecomp/`,
and drop `productExists` from `G0Split.MissingPieces`. Note `NumberField L` is unused, and the
piece's docstring remark "geometric integrality of products is not in Mathlib" is obsolete.
Report: docs/research/g0-product.md; log: scratch/g0-product/log.md.
