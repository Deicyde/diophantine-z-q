
/-! ## unif-dims: `ProductCotangent` closed; `ProductHodgeLattice` from `TangentDimAtOrigin` and T35 -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- **`ProductCotangent`, proved** (`productCotangent_aux`, `PC.lean`). -/
theorem productCotangent : ProductCotangent := productCotangent_aux

/-- **metrization's `ProductHodgeLattice` from hodge-lattice's `TangentDimAtOrigin` and the
textbook leaf T35 (proved).** -/
theorem productHodgeLattice_of_tangentDim (hT : TangentDimAtOrigin)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of_cotangent productCotangent hT hT35

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.productCotangent
#print axioms ZInQ.UnifDims.productHodgeLattice_of_tangentDim
