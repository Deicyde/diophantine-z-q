
/-! ## unif-dims: `DetLatticeProd` closed; `ProductHodgeLattice` from `ProductCotangent`,
`TangentDimAtOrigin` and T35 -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- **`DetLatticeProd`, proved** (`detLatticeProd_aux`, `DetProd.lean`). -/
theorem detLatticeProd : DetLatticeProd := detLatticeProd_aux

/-- **`ProductHodgeLattice` from `ProductCotangent`, hodge-lattice's `TangentDimAtOrigin` and T35
(proved).** -/
theorem productHodgeLattice_of_cotangent (hPC : ProductCotangent) (hT : TangentDimAtOrigin)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of_tangent hPC detLatticeProd hT hT35

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.detLatticeProd
#print axioms ZInQ.UnifDims.productHodgeLattice_of_cotangent
