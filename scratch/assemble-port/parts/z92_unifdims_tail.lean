/-! ## g0-assemble3: unif-dims' Leaves-world closing theorem (`scratch/unif-dims/build_leaves.py`, the `tail` string,
verbatim), and its instance with infra-smooth-dim's `tangentDimAtOrigin` (part e25). -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- Integration check: Leaves.lean's glue piece 5 (`GluePieces.productModelHeight`) from
metrization's `AnalyticUniformizationOfDim` (which follows from T35 in the kernel world) and
hodge-lattice's `TangentDimAtOrigin`. -/
theorem productModelHeight_of_leaves (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits ZInQ.ProductUnif.productUnifSplits
    (ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
      (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
      (productUnifDims_of_unifOfDim hU) ZInQ.Metrization2.productLocalStructure
      (productHodgeLattice_of productCotangent detLatticeProd
        (cotangentRank_of_tangentDim (tangentDim_of_abVar hT dimBaseChange)) hU))

/-- (g0-assemble3) product-height's S-alg `ProductMetrizationOfProductUnif` from the leaf
`AnalyticUniformizationOfDim` alone (`TangentDimAtOrigin` is infra-smooth-dim's theorem). -/
theorem productMetrizationOfProductUnif_of_unifOfDim
    (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
    (hodgeLatticeTheorem_of_tangent tangentDimAtOrigin dimBaseChange)
    (productUnifDims_of_unifOfDim hU) ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of productCotangent detLatticeProd
      (cotangentRank_of_tangentDim (tangentDim_of_abVar tangentDimAtOrigin dimBaseChange)) hU)

/-- (g0-assemble3) `ProductModelHeight` (the `GluePieces` field) from the leaf
`AnalyticUniformizationOfDim` alone. -/
theorem productModelHeight_of_unifOfDim (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_leaves hU tangentDimAtOrigin

end ZInQ.UnifDims
