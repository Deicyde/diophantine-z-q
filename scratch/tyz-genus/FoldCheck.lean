import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.TYZLemma28Sym
import ZInQKernel.Contrib.OneProof.TYZThm11Genus
import ZInQKernel.Contrib.OneProof.TYZThm21PairsOne

/-! tyz-genus: the manual fold (`hL29` is a top-level argument of `frozenTarget`, so autofold does not apply):
`frozenTarget` with `hL29 : H29Split.TYZLemma29PrintedNe3` (TYZ Lemma 2.9 as printed, `n ≠ 3`) replaced by
`h21 : H29Genus.TYZThm21Pairs` (TYZ Theorem 2.1 for every pair), using the proved TYZ Lemma 2.8
(`TYZGenusFold.tyzLemma28Sym`). Count-neutral (one printed TYZ leaf for one). For `Main.lean`: replace the binder
`(hL29 : H29Split.TYZLemma29PrintedNe3)` by `(h21 : ZInQ.Contrib.TYZDecomp.H29Genus.TYZThm21Pairs)` and the
argument `hL29` by `(ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21Pairs h21)`, and add the import
`ZInQKernel.Contrib.OneProof.TYZLemma28Sym`. -/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, with TYZ Theorem 2.1 for every pair in place of TYZ Lemma 2.9** (the body of `frozenTarget`
with the one argument changed). -/
theorem frozenTarget_thm21
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h11 : TYZThm11Integral)
    (h21 : H29Genus.TYZThm21Pairs)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open41 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists
      (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21Pairs h21) ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

/-- The same theorem, as an instance of the current `frozenTarget` (a check that nothing else changed). -/
theorem frozenTarget_thm21' (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15)
    (l : HDec.HSyn.OpenAddedLeaves20) (h11 : TYZThm11Integral) (h21 : H29Genus.TYZThm21Pairs)
    (hCM : _root_.T5Glue.ShimuraMainCM) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0) (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l h11 (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21Pairs h21)
    hCM h33 hBFH hGZ

/-- **Variant B (count-neutral): `h11` and `hL29` replaced by the complex form of TYZ Theorem 2.1 and
`𝓛(1)² = 1`.** For `Main.lean`: replace the binders `(h11 : TYZThm11Integral)` and
`(hL29 : H29Split.TYZLemma29PrintedNe3)` by `(h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)` and
`(hL1 : TYZLcalOne)`, and the arguments `h11`, `hL29` by
`(ZInQ.Contrib.TYZGenusFold.tyzThm11Integral_of_thm21C h21C hL1)` and
`(ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C)`; add the import
`ZInQKernel.Contrib.OneProof.TYZThm11Genus`. -/
theorem frozenTarget_thm21C
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)
    (hL1 : TYZLcalOne)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l (ZInQ.Contrib.TYZGenusFold.tyzThm11Integral_of_thm21C h21C hL1)
    (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C) hCM h33 hBFH hGZ

/-- **Variant C (−1, pending a reading of TYZ Theorem 2.1 at `n = 1`): `h11` and `hL29` replaced by the one
statement `TYZThm21PairsC1`.** For `Main.lean`: replace the binders `(h11 : TYZThm11Integral)` and
`(hL29 : H29Split.TYZLemma29PrintedNe3)` by `(h21 : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC1)`, and the arguments
`h11`, `hL29` by `(ZInQ.Contrib.TYZGenusFold.tyzThm11Integral_of_C1 h21)` and
`(ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_C1 h21)`; add the import
`ZInQKernel.Contrib.OneProof.TYZThm21PairsOne`. -/
theorem frozenTarget_thm21One
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves20)
    (h21 : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC1)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.OneProof.frozenTarget r t l (ZInQ.Contrib.TYZGenusFold.tyzThm11Integral_of_C1 h21)
    (ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_C1 h21) hCM h33 hBFH hGZ

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_thm21
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_thm21'
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_thm21C
#print axioms ZInQ.Contrib.TYZChain.frozenTarget_thm21One
