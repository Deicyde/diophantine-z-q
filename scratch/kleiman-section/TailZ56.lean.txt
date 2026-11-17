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

#print axioms HDec.HSyn.sixContactMin_of_open49
