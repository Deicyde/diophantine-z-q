/-! ## metrization2: g0-heightadd's `HeightAdditivity` with the smaller hypotheses

Compared with metrization's `heightAdditivity_of_metrization_v3`: the leaf
`AnalyticUniformizationOfDim` is replaced by leaf-push2's T35 `UniformizationExists` (already a
field `t35` of `HSyn.TextbookLeaves`), and the two glue Props `JacDetNondegenerate` and
`ProductLocalStructure` by the one glue Prop `ProductMapLocalStructure`. -/

namespace HSyn.G0Split

theorem heightAdditivity_of_metrization_v4 (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hML : ZInQ.Metrization2.ProductMapLocalStructure)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) : HeightAdditivity :=
  heightAdditivity_of_metrization_v3 hN1 h5 hU hH
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35)
    (ZInQ.Metrization2.jacDetNondegenerate_of hML)
    (ZInQ.Metrization2.productLocalStructure_of hML) hPL

/-- **`HeightAdditivity` with `ProductMapLocalStructure` proved**: from N1, H5, def-faltings'
`AnalyticUniformizationUnique` and `HodgeLatticeTheorem`, T35 and metrization's
`ProductHodgeLattice`. -/
theorem heightAdditivity_of_metrization_v5 (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) : HeightAdditivity :=
  heightAdditivity_of_metrization_v4 hN1 h5 hU hH hT35
    ZInQ.Metrization2.productMapLocalStructure hPL

end HSyn.G0Split

/-- **`MetrizationExists` from def-faltings' `HodgeLatticeTheorem` and T35 alone.** -/
theorem ZInQ.Metrization2.metrizationExists_of_uniformizationExists
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem) (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.G0HeightAdd.MetrizationExists :=
  ZInQ.Metrization2.metrizationExists_of_productMap hH
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35)
    ZInQ.Metrization2.productMapLocalStructure

#print axioms ZInQ.Metrization2.jacDetNondegenerate_of
#print axioms ZInQ.Metrization2.productLocalStructure_of
#print axioms ZInQ.Metrization2.metrizationExists_of_productMap
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
#print axioms HSyn.G0Split.heightAdditivity_of_metrization_v4
#print axioms ZInQ.Metrization2.productMapLocalStructure
#print axioms ZInQ.Metrization2.jacDetNondegenerate
#print axioms ZInQ.Metrization2.productLocalStructure
#print axioms HSyn.G0Split.heightAdditivity_of_metrization_v5
#print axioms ZInQ.Metrization2.metrizationExists_of_uniformizationExists
