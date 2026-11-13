
/-! ## unif-dims: S-alg and P2 from T35, `ProductCotangent` and `TangentDimAtOrigin` -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice

/-- **S-alg (`ProductMetrizationOfProductUnif`) from T35, `ProductCotangent` and
`TangentDimAtOrigin` (proved).** product-unif's `productMetrizationOfProductUnif_of_local` with
`HodgeLatticeTheorem` from hodge-lattice (`TangentDimAtOrigin`, `DimBaseChange` proved here),
`ProductUnifDims` from T35, metrization2's `productLocalStructure`, and `ProductHodgeLattice`
from `ProductCotangent`. -/
theorem productMetrizationOfProductUnif_of_cotangent (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hPC : ProductCotangent) (hT : TangentDimAtOrigin) :
    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
    (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
    (productUnifDims_of_uniformizationExists hT35)
    ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of_cotangent hPC hT hT35)

/-- **Glue piece 5 of `GluePieces` (P2, `ProductModelHeight`) from T35, `ProductCotangent` and
`TangentDimAtOrigin` (proved).** -/
theorem productModelHeight_of_cotangent (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hPC : ProductCotangent) (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductUnif.productModelHeight_of_local (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
    (productUnifDims_of_uniformizationExists hT35) ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of_cotangent hPC hT hT35)

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.productMetrizationOfProductUnif_of_cotangent
#print axioms ZInQ.UnifDims.productModelHeight_of_cotangent
