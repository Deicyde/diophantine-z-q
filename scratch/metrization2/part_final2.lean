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

end HSyn.G0Split

#print axioms ZInQ.Metrization2.jacDetNondegenerate_of
#print axioms ZInQ.Metrization2.productLocalStructure_of
#print axioms ZInQ.Metrization2.metrizationExists_of_productMap
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
#print axioms HSyn.G0Split.heightAdditivity_of_metrization_v4
