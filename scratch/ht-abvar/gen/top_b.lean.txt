
/-- Copy of `openAddedLeaves18_of_OpenAddedLeaves22_pz_c8` (generated above) without its unused arguments `t`, `n`
(the copy reads neither; `n : OpenAddedLeaves22PZ` is the bundle that carries the Picard rows). -/
theorem openAddedLeaves18_ht (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs) : OpenAddedLeaves18PZC8 where
  egaIV_8_10_5_xii := _root_.ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof
  c8 := c8

/-- Copy of c8-conrad2's `sixContactMin_of_open45_pz_eb_c8` without the added bundle `l` (only its unused pass-through
to `openAddedLeaves18_of_OpenAddedLeaves22_pz_c8`). -/
theorem sixContactMin_of_open45_pz_eb_ht (r : OpenResearchLeaves31EB) (t : OpenTextbookLeaves16)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open37_hf_gm_pz_eb_c8
    (openResearchLeaves27_of_OpenResearchLeaves28_gm_eb
      (openResearchLeaves28_of_OpenResearchLeaves29_gm_eb (openResearchLeaves29GM_of_OpenResearchLeaves31_eb r)))
    (openTextbookLeaves13HF_of_open16_P t r.neronSchemeExtensionDedekind hP)
    (openAddedLeaves18_ht c8)

/-- Copy of `sixContactMin_of_open72` (TailZ79, the current top) with the three swaps: C8 by local algebraicity
(`c8`), Poincaré from the textbook leaf (`hP`), and `hodgeTateDecompAbVar` from the manuscript's route
(`hS`, `hT`, `hH`). No added bundle: the Picard rows are not hypotheses. -/
theorem sixContactMin_of_open72_ht (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) (c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs)
    (hS : _root_.DeRhamScholze.ScholzeDeRhamAlg) (hT : _root_.T10Etale.T10_TateDuality)
    (hH : _root_.DeRhamScholze.HTAbVar.HodgeNumberH1AbVar) : ZInQ.SixContactMin :=
  let t16 := openTextbookLeaves16_of_OpenTextbookLeaves17 (openTextbookLeaves17_of_OpenTextbookLeaves18 t)
  sixContactMin_of_open45_pz_eb_ht (openResearchLeaves31_of_OpenResearchLeaves32_eb_cf (openResearchLeaves32_of_OpenResearchLeaves33_eb_cf (openResearchLeaves33_of_OpenResearchLeaves34_eb_cf (openResearchLeaves34_of_OpenResearchLeaves35_eb_cf (openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_ht (openResearchLeaves36EBCF_of_OpenResearchLeaves53 r t) (_root_.DeRhamScholze.HTAbVar.hodgeTateDecompAbVar_of_scholze hS hT hH)) t16) t16))) t16 hP c8

/-! ### Hand-fold shape: the next generation of bundles (no Picard rows) -/

/-- `OpenTextbookLeaves18` (empty) with Poincaré's theorem (c8-conrad2's `OpenTextbookLeaves19C8`). -/
structure OpenTextbookLeaves19HT : Prop where
  /-- Poincaré complete reducibility, complement form (Milne 1986 Prop. 12.1; manuscript L865, ELLIOT). -/
  poincareComplement : _root_.ZInQ.Contrib.AVB1.PoincareComplement

/-- `OpenAddedLeaves27` without `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ`, with c8-conrad3's two
printed C8 leaves, derham-scholze's two leaves and the Hodge numbers. -/
structure OpenAddedLeaves28HT : Prop where
  /-- CITED (L761): Conrad, author preprint 2011, App. B, pp. 32-33, base field `ℚ_p` (unread; unrefereed). -/
  conradAppBQp : _root_.HDec.G0Galois.C8Conrad.ConradAppBQp
  /-- DEPARTURE (c8-conrad3; uncited step L763-764): Tate 1967 §3.3 Thm 2 for the completion of `K^{ur}`. -/
  tateTwistInvariantsInertia : _root_.HDec.G0Galois.C8Conrad.TateTwistInvariantsInertia
  /-- CITED (L736-737, L10953-10965): Scholze 2013 Cor. 1.8 + Thms 9.1, 9.3, algebraic form (derham-scholze). -/
  scholzeDeRhamAlg : _root_.DeRhamScholze.ScholzeDeRhamAlg
  /-- CITED (L10966-10970): Milne, AV v2.00 Part I Thm 12.1(a) / Milne 1986 Thm 15.1(a) (t10-etale). -/
  t10TateDuality : _root_.T10Etale.T10_TateDuality
  /-- ELLIOT (L10996, uncited) through Scholze's filtered comparison: `dim Fil¹ D_dR(H¹_ét(A)) = [F:ℚ_p] g`
  (ht-abvar). -/
  hodgeNumberH1AbVar : _root_.DeRhamScholze.HTAbVar.HodgeNumberH1AbVar

theorem c8Leaves_of_OpenAddedLeaves28HT (n : OpenAddedLeaves28HT) : _root_.HDec.G0Galois.C8Conrad.C8Leaves where
  conradAppBQp := n.conradAppBQp
  tateTwistInvariantsInertia := n.tateTwistInvariantsInertia

/-- **The next top theorem (hand-fold shape)**: `ZInQ.SixContactMin` without the Picard rows. -/
theorem sixContactMin_of_open73HT (r : OpenResearchLeaves53) (t : OpenTextbookLeaves19HT) (l : OpenAddedLeaves28HT) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open72_ht r ⟨⟩ t.poincareComplement (_root_.HDec.G0Galois.C8Conrad.c8Inputs_of_leaves (c8Leaves_of_OpenAddedLeaves28HT l)) l.scholzeDeRhamAlg
    l.t10TateDuality l.hodgeNumberH1AbVar

end HSyn
end HDec

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Dry run: Theorem 1.1 without the Picard rows** (copy of `ZInQ.OneProof.frozenTarget`, Main.lean, with
`sixContactMin_of_open73HT`; the CR3-side hypotheses verbatim). -/
theorem _root_.ZInQ.OneProof.frozenTarget_ht
    (r : HDec.HSyn.OpenResearchLeaves53) (t : HDec.HSyn.OpenTextbookLeaves19HT) (l : HDec.HSyn.OpenAddedLeaves28HT)
    (h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)
    (hCM : ZInQ.Contrib.HCMLattice.ShimuraThm54Local)
    (h33c : ZInQ.H33D1.TYZThm33CurveSome)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZss : ZInQ.GZSplitUnique.GrossZagierCurveCdSplitSome) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open73HT r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX (ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)) (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C (ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) (ZInQ.H33D1.tyzThm33_of_curveSome (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) h33c))
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMLattice.shimuraMainCM_of_local hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg (ZInQ.GZSplitUnique.grossZagierAlgOptCd_of_splitSome hGZss) ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget_ht
#print axioms HDec.HSyn.sixContactMin_of_open73HT
#print axioms HDec.HSyn.sixContactMin_of_open72_ht
