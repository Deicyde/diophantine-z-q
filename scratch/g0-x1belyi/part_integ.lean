
/-! ## Integration: Split.lean's `glueOutputs_of_leaves` with `hBelyi` discharged -/

namespace HSyn

open G0Split

/-- `glueOutputs_of_leaves` of g0-split with the hypothesis `X1BelyiOnModel` replaced by the two
x1-belyi leaves T1 (`X1Belyi.TorsionStructure`) and T2 (`X1Belyi.GoodReductionUnramified`). -/
theorem glueOutputs_of_leaves_x1 (r : ResearchLeaves) (t : TextbookLeaves)
    (hR18 : R18_JavanpeykarConcrete) (hR22 : R22_PazukiConcrete)
    (hT : X1Belyi.TorsionStructure) (hG : X1Belyi.GoodReductionUnramified)
    (hDimF : DimFinite) (hDim : DimBaseChange) (hSimp : FibreSimple)
    (hAdd : HeightAdditivity) (hBC : StableHeightBaseChange) (hProdE : ProductExists)
    (hRev : ReverseIsogeny) (hThetaPt : ThetaPointOfFibre) (hMod : ModularConstituent) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul :=
  glueOutputs_of_leaves r t hR18 hR22 hDimF hDim (G0X1Belyi.x1BelyiOnModel_of_leaves hT hG) hSimp
    hAdd hBC hProdE hRev hThetaPt hMod

/-- The same, to `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves_x1 (r : ResearchLeaves) (t : TextbookLeaves)
    (hR18 : R18_JavanpeykarConcrete) (hR22 : R22_PazukiConcrete)
    (hT : X1Belyi.TorsionStructure) (hG : X1Belyi.GoodReductionUnramified)
    (hDimF : DimFinite) (hDim : DimBaseChange) (hSimp : FibreSimple)
    (hAdd : HeightAdditivity) (hBC : StableHeightBaseChange) (hProdE : ProductExists)
    (hRev : ReverseIsogeny) (hThetaPt : ThetaPointOfFibre) (hMod : ModularConstituent) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves_x1 r t hR18 hR22 hT hG hDimF hDim hSimp
    hAdd hBC hProdE hRev hThetaPt hMod)

end HSyn

#print axioms HSyn.glueOutputs_of_leaves_x1
#print axioms HSyn.sixContactMin_of_leaves_x1
