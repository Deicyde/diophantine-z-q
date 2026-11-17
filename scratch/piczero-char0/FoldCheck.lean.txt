import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZeroReroute

/-! piczero-char0 fold check (manual fold; autofold cannot express a reroute).

The next bundle generation `OpenAddedLeaves21` is `OpenAddedLeaves20` without the GLUE field `picZeroAbVar` and with
three LEAF fields, `picLocFinType`, `identityComponentLFT`, `kleimanPicZeroProper`, from which
`PicZeroChar0.picZeroAbVar0_of_leaves` proves the characteristic-`0` form that the rerouted chain
(`PicZeroAbVarCharZeroReroute.lean`) reads. `ZInQ.OneProof.frozenTarget_pz` is `frozenTarget` with the added bundle
`OpenAddedLeaves21`; its body is `frozenTarget`'s with `sixContactMin_of_open41` replaced by
`sixContactMin_of_open42_pz`. This is the content of the integrator's `TailZ49` and `Main` switch. -/

namespace HDec.HSyn

/-- **The added leaves still open** (piczero-char0): `OpenAddedLeaves20` without `picZeroAbVar` (used only in
characteristic `0`, `PicZeroChar0.picZeroAbVar0_of_leaves`), with three printed leaves added. 6 fields. -/
structure OpenAddedLeaves21 : Prop where
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic, L4, printed form (single leaf): Mumford's `ē_n` on `A[n] × Pic⁰[n]` (Mumford §20 and §23; Milne 1986
  §16; locators UNVERIFIED). -/
  weilPairingMumford : _root_.T09Pic.WeilPairingMumford
  /-- pic-dict: for L ample every L' in Pic0(X) is t_x^*L (x) L^-1, X an abelian variety over an algebraically closed
  field (Mumford section 8 Thm 1; locator UNVERIFIED). -/
  mumfordPhiSurjectiveAC : _root_.PicDict.MumfordPhiSurjectiveAC
  /-- pic-dict: a scheme representing `Pic_{A/K}` of an abelian variety `A` over a field `K` is locally of finite type
  (Murre 1964 / Oort 1962, BLR, *Néron models*, 8.2 Thm 3; Kleiman, *The Picard scheme*, Thm 9.4.8; any representing
  object by Yoneda; locators UNVERIFIED). -/
  picLocFinType : _root_.PicDict.PicLocFinType
  /-- pic-dict: the identity component of a group scheme locally of finite type over a field is an open,
  geometrically irreducible subgroup (SGA 3 VI_A 2.4; Stacks 0B7R; locators UNVERIFIED). -/
  identityComponentLFT : _root_.PicDict.IdentityComponentLFT
  /-- pic-fix: for `X` proper and geometrically normal over a field `K`, the identity component of `Pic_{X/K}` is
  proper (Kleiman, *The Picard scheme*, Thm 9.5.4; locator UNVERIFIED); stated for every representing scheme. -/
  kleimanPicZeroProper : _root_.PicFix.KleimanPicZeroProper

/-- `OpenAddedLeaves20PZ` from `OpenAddedLeaves21`: `picZeroAbVar` in characteristic `0` from the three leaves and
Cartier's theorem (`cartierSmooth_proof`). -/
theorem openAddedLeaves20PZ_of_OpenAddedLeaves21 (n : OpenAddedLeaves21) : OpenAddedLeaves20PZ where
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := _root_.PicZeroChar0.picZeroAbVar0_of_leaves n.picLocFinType n.identityComponentLFT
    n.kleimanPicZeroProper
  weilPairingMumford := n.weilPairingMumford
  mumfordPhiSurjectiveAC := n.mumfordPhiSurjectiveAC

/-- **G0 with only the open leaves and the open glue** (piczero-char0). -/
theorem sixContactMin_of_open42_pz (r : OpenResearchLeaves29) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves21) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open41_pz r t (openAddedLeaves20PZ_of_OpenAddedLeaves21 l)

/-- `OpenAddedLeaves20PZ` is `OpenAddedLeaves20` with only `picZeroAbVar` weakened (field by field). -/
theorem openAddedLeaves20PZ_of_20 (n : OpenAddedLeaves20) : OpenAddedLeaves20PZ where
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := _root_.PicZeroChar0.picZeroAbVar0_of_picZeroAbVar n.picZeroAbVar
  weilPairingMumford := n.weilPairingMumford
  mumfordPhiSurjectiveAC := n.mumfordPhiSurjectiveAC

end HDec.HSyn

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open** (after the piczero-char0 fold). -/
theorem _root_.ZInQ.OneProof.frozenTarget_pz
    (r : HDec.HSyn.OpenResearchLeaves29) (t : HDec.HSyn.OpenTextbookLeaves15) (l : HDec.HSyn.OpenAddedLeaves21)
    (h11 : TYZThm11Integral)
    (hfx : H29Split.TYZTestVectorExists) (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hP23 : H29Split.TYZProp23Printed)
    (hCM : _root_.T5Glue.ShimuraMainCM)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) (hQ : ZInQ.GZAlg.Gamma0QExpansion) (hW : ZInQ.CdOpt.EtaW32Character) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open42_pz r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof hfx hL29 ZInQ.Contrib.T21Proof.tyzThm21At31 hP23) hCM h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed hCM (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ hQ hW)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget_pz
#print axioms HDec.HSyn.sixContactMin_of_open42_pz
