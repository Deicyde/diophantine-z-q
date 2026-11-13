
/-! ## unif-dims: S-alg and P2 from T35 and `TangentDimAtOrigin` alone -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice

/-- **S-alg (`ProductMetrizationOfProductUnif`) from T35 and `TangentDimAtOrigin` (proved).** -/
theorem productMetrizationOfProductUnif_of_tangentDim (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hT : TangentDimAtOrigin) : ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of_cotangent hT35 productCotangent hT

/-- **Glue piece 5 of `GluePieces` (P2, `ProductModelHeight`) from the textbook leaf T35 and
hodge-lattice's `TangentDimAtOrigin` (proved).** -/
theorem productModelHeight_of_tangentDim (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_cotangent hT35 productCotangent hT

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim
#print axioms ZInQ.UnifDims.productModelHeight_of_tangentDim
