
/-! ## Handwritten top section (c8-conrad2): from the current top's bundles, the new textbook leaf `hP` (Poincaré)
and the C8 inputs `c8`, with the Picard rows read only by consumer (iii) (`openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf … l26`, the `hodgeTateDecompAbVar → r10` path). -/

namespace HDec
namespace HSyn

/-- Copy of `sixContactMin_of_open45_pz_eb` (EichlerBoundCopy L3291): the textbook bundle with Poincaré's theorem as
a leaf (`openTextbookLeaves13HF_of_open16_P`, consumer (ii) removed) and the added bundle without the Weil-pairing
fields (`openAddedLeaves18_of_OpenAddedLeaves22_pz_c8`, consumer (i) removed). -/
theorem sixContactMin_of_open45_pz_eb_c8 (r : OpenResearchLeaves31EB) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves22PZ)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open37_hf_gm_pz_eb_c8
    (openResearchLeaves27_of_OpenResearchLeaves28_gm_eb
      (openResearchLeaves28_of_OpenResearchLeaves29_gm_eb (openResearchLeaves29GM_of_OpenResearchLeaves31_eb r)))
    (openTextbookLeaves13HF_of_open16_P t r.neronSchemeExtensionDedekind hP)
    (openAddedLeaves18_of_OpenAddedLeaves22_pz_c8 c8 t l)

/-- Copy of `sixContactMin_of_open48_eb_k954` (TailZ69 L74). -/
theorem sixContactMin_of_open48_eb_k954_c8 (r : OpenResearchLeaves31EB) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves26)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open45_pz_eb_c8 r t (openAddedLeaves22PZ_of_OpenAddedLeaves26 l) hP c8

/-- Copy of `sixContactMin_of_open70` (TailZ77 L110). -/
theorem sixContactMin_of_open70_c8 (r : OpenResearchLeaves51) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs) :
    ZInQ.SixContactMin :=
  let t16 := openTextbookLeaves16_of_OpenTextbookLeaves17 (openTextbookLeaves17_of_OpenTextbookLeaves18 t)
  let l26 := openAddedLeaves26_of_OpenAddedLeaves27 l
  sixContactMin_of_open48_eb_k954_c8 (openResearchLeaves31_of_OpenResearchLeaves32_eb_cf (openResearchLeaves32_of_OpenResearchLeaves33_eb_cf (openResearchLeaves33_of_OpenResearchLeaves34_eb_cf (openResearchLeaves34_of_OpenResearchLeaves35_eb_cf (openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf (openResearchLeaves36EBCF_of_OpenResearchLeaves51 r t) t16 l26) t16) t16))) t16 l26 hP c8

/-- Copy of `sixContactMin_of_open71` (TailZ78 L102), the current top. -/
theorem sixContactMin_of_open71_c8 (r : OpenResearchLeaves52) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open70_c8 (openResearchLeaves51_of_OpenResearchLeaves52 r) t l hP c8

end HSyn
end HDec

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Dry run: Theorem 1.1 with the C8 and Poincaré swaps** (copy of `ZInQ.OneProof.frozenTarget`, Main.lean, with
`sixContactMin_of_open71_c8` and the two new inputs). -/
theorem _root_.ZInQ.OneProof.frozenTarget_c8
    (r : HDec.HSyn.OpenResearchLeaves52) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves27)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs)
    (h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)
    (hCM : ZInQ.Contrib.HCMLattice.ShimuraThm54Local)
    (h33c : ZInQ.H33D1.TYZThm33CurveSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZss : ZInQ.GZSplitUnique.GrossZagierCurveCdSplitSome) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open71_c8 r t l hP c8)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) (ZInQ.H33D1.tyzThm33_of_curveSome (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) h33c))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSplitUnique.grossZagierAlgOptCd_of_splitSome hGZss) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget_c8
#print axioms HDec.HSyn.sixContactMin_of_open71_c8
