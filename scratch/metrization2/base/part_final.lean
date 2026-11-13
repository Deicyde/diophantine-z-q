
/-! ## metrization: what remains of `ProductMetrizationGeo` and `HeightAdditivity` -/

namespace ZInQ.Metrization

/-- **`ProductMetrizationGeo` from `JacDetDescends`, `ProductUniformization` and
`ProductHodgeCompat`** (`ProductLatticeFacts` proved). -/
theorem productMetrizationGeo_of' (hJ : JacDetDescends) (hPU : ProductUniformization)
    (hPC : ProductHodgeCompat) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of hJ hPU productLatticeFacts hPC

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization.** From the leaf N1, the bundle field `h5`,
def-faltings' stated `AnalyticUniformizationUnique` and `HodgeLatticeTheorem`, the leaf
`AnalyticUniformizationOfDim`, and the glue `JacDetDescends`, `JacDetNondegenerate`,
`ProductUniformization`, `ProductHodgeCompat`. (`MetrizationDimUnique` and
`ProductLatticeFacts` are proved.) -/
theorem heightAdditivity_of_metrization (hN1 : ZInQ.H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim) (hJ : ZInQ.Metrization.JacDetDescends)
    (hN : ZInQ.Metrization.JacDetNondegenerate) (hPU : ZInQ.Metrization.ProductUniformization)
    (hPC : ZInQ.Metrization.ProductHodgeCompat) : HeightAdditivity :=
  heightAdditivity_of_geo hN1 h5 hU ZInQ.Metrization.metrizationDimUnique
    (ZInQ.Metrization.metrizationExists_of hH hUD hJ hN)
    (ZInQ.Metrization.productMetrizationGeo_of' hJ hPU hPC)

end HSyn.G0Split

#print axioms ZInQ.Metrization.productMetrizationGeo_of'
#print axioms HSyn.G0Split.heightAdditivity_of_metrization
