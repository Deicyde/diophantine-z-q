import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.H.TailZ55
import ZInQKernel.Contrib.OneProof.KleimanPicZeroProperQuot

/-! # OneProof H, kleiman-section (hand fold): `sixContactMin_of_open49`

Field replaced: `kleimanPicZeroProper : PicFix.KleimanPicZeroProper` of `OpenAddedLeaves25` (stated over the tree's
`picardFunctor`, no quotient by `Pic(T)`; rated GLUE by the latest review). It is replaced by Kleiman 9.5.4 over
Kleiman's own functor in its weakest reading, `KleimanSection.KleimanPicZeroProperPrinted` (`X` also geometrically
integral, projective and with a `K`-point). That leaf is weaker than the field, so it cannot fill it; instead the
conversion goes one step down the chain, to `OpenAddedLeaves22PZ`, whose `picZeroAbVar` is filled by
`KleimanSection.picZeroAbVar0_of_printed` from `picLocFinType_proof`, `identityComponentLFT_proof` and the new
leaf. One LEAF field out (counted GLUE by the review), one LEAF field in. -/

namespace HDec

namespace HSyn

/-- `OpenAddedLeaves25` with `kleimanPicZeroProper` replaced by its weakest-reading printed form over Kleiman's
functor (kleiman-section). 2 fields. -/
structure OpenAddedLeaves26 : Prop where
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). With the next three replaces `t09SymmIsogenyExists`. -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- kleiman-section: for `X` proper, geometrically integral, geometrically normal and projective over a field `K`
  with a `K`-point, the identity component of any scheme representing Kleiman's `Pic_{(X/K)(fppf)}` (fppf
  sheafification of `T ↦ Pic(X_T)/Pic(T)`) is proper (Kleiman, *The Picard scheme*, Thm 9.5.4; locator UNVERIFIED). -/
  kleimanPicZeroProperPrinted : _root_.KleimanSection.KleimanPicZeroProperPrinted

/-- `OpenAddedLeaves22PZ` from `OpenAddedLeaves26`: `picZeroAbVar` (characteristic `0`) from the two proved
leaves and Kleiman 9.5.4 over Kleiman's functor. -/
theorem openAddedLeaves22PZ_of_OpenAddedLeaves26 (n : OpenAddedLeaves26) : OpenAddedLeaves22PZ where
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := _root_.KleimanSection.picZeroAbVar0_of_printed _root_.PicLFT.picLocFinType_proof
    _root_.IdCompLFT.identityComponentLFT_proof n.kleimanPicZeroProperPrinted

/-- **G0 with only the open leaves and the open glue** (kleiman-section; hand fold). -/
theorem sixContactMin_of_open49 (r : OpenResearchLeaves31) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves26) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open45_pz r t (openAddedLeaves22PZ_of_OpenAddedLeaves26 l)

end HSyn

end HDec


/-! Check only (not part of the module): `frozenTarget` with `Main.lean` switched to `sixContactMin_of_open49`. -/
namespace ZInQ.Contrib.TYZChain
open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus
theorem frozenTarget_kleimanSection
    (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves26)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open49 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29 ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.Contrib.TYZChain.frozenTarget_kleimanSection
