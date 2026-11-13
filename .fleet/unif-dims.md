# unif-dims (fleet summary)

**Verdict: both targets are proved, adding no new leaf and no new open glue.**

1. **`ProductUnifDims` is proved from T35.** T35 is `UniformizationExists`, already
   `TextbookLeaves.t35`.
   - Theorem: `ZInQ.UnifDims.productUnifDims_of_uniformizationExists`.
   - The dimension of a full-lattice uniformization `ℂ^g → G` is fixed by the group alone:
     `#G[2] = 2^{2g}`. T35 gives one uniformization of dimension `dim A`, so `g = dim A`.
   - metrization2's `jacDetNondegenerate` gives the nonsingularity half.
   - The statement's product-form hypotheses turn out to be unused.
2. **`ProductHodgeLattice` (infra-stalks had not closed it) is proved from `TangentDimAtOrigin`
   and T35.** `TangentDimAtOrigin` is hodge-lattice's existing named open Prop.
   - Theorem: `productHodgeLattice_of_tangentDim`.
   - It goes through two new glue Props, both proved:
     - `DetLatticeProd`: the determinant lattice of a direct sum, with indices multiplicative
       (generalized Laplace expansion plus `FractionalIdeal.absNorm`);
     - `ProductCotangent`: the cotangent space and conormal lattice `ω` of a product model.
       The ingredients are cotangent maps, functoriality of `ω`, retractions `x ↦ (x,1)`, and
       infra-stalks' stalk lemmas for fibre products.
   - hodge-lattice's `DimBaseChange` is proved along the way (from g0-dim).
3. **Consequence: glue piece 5 (P2, `ProductModelHeight`) and S-alg follow from T35 and
   `TangentDimAtOrigin` alone.** `TangentDimAtOrigin` is shared with `HodgeLatticeTheorem`.
   - Theorems: `productModelHeight_of_tangentDim` and
     `productMetrizationOfProductUnif_of_tangentDim`.

**What compiles.** Everything is in `scratch/unif-dims/`. Every file passes `lake env lean` with
0 errors, no sorry and no axiom, and its `#print axioms` lists only the standard axioms.

| file | imports | built by | time | content |
|---|---|---|---|---|
| `Torsion.lean` | Mathlib | — | — | the 2-torsion count |
| `DetProd.lean` | kernel `HodgeLattice` | — | — | `DetLatticeProd` |
| `PC.lean` | — | `build_pc.sh` | — | `ProductCotangent` |
| `UnifDims.lean` | kernel `LeafPush2.T` and `HodgeLattice` | `build.sh` | 20 s | all results |
| `Combined.lean` | — | `build_combined.py` | 25 s | product-height's and product-unif's files plus metrization2's: S-alg and P2 |
| `LeavesIntegrated.lean` | — | `build_leaves.py` | 8 min | not committed: P2 over `scratch/h-decomposition/Leaves.lean`'s own definitions |

**Finding.** In `Leaves.lean`, T35 is stated over `PkgI3.AbVar`, with leaf-push2's own copy of the
model layer, while def-faltings' models use the distinct `ZInQ.DefFaltings.AbVar`. So T35 cannot be
applied to group models there without an `AbVar` bridge.
- The Leaves check is therefore stated from metrization's `AnalyticUniformizationOfDim`, and it
  compiles.
- In the kernel the two structures are the same, and T35 ⇒ `AnalyticUniformizationOfDim` compiles.

**What remains.**
- Nothing new is needed for P2 beyond `TangentDimAtOrigin`: dimension theory of varieties, open,
  already named.
- Adopting the files into the kernel needs product-unif's, product-height's, metrization2's and
  infra-stalks' pieces adopted first.

**Report and log.** The report is `docs/research/unif-dims.md`; the log is
`scratch/unif-dims/log.md`. One model review was done; there was no human review.
