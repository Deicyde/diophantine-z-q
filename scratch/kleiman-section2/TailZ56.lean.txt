import ZInQKernel.OneProof.H.TailZ55
import ZInQKernel.Contrib.OneProof.KleimanPicZero954

/-! # OneProof H, kleiman-section2 (hand fold): `sixContactMin_of_open49`

Supersedes kleiman-section's draft of this module (same names; integrate only one). Field replaced:
`kleimanPicZeroProper : PicFix.KleimanPicZeroProper` of `OpenAddedLeaves25` (`X` only proper and geometrically
normal, stronger than Kleiman 9.5.4; rated GLUE by the latest review). It is replaced by Kleiman 9.5.4 as printed,
`KleimanSection2.KleimanPicZeroProper954` (`X` projective, geometrically integral, geometrically normal, with a
`K`-point; representability over locally Noetherian test schemes). That leaf is weaker than the field, so it cannot
fill it; the conversion goes one step down the chain, to `OpenAddedLeaves22PZ` (TailZ53–55 only pass the field down
to `picZeroAbVar0_of_leaves`), whose `picZeroAbVar` is filled by `KleimanSection2.picZeroAbVar0_of_954` (with
`picLocFinType_proof`, `identityComponentLFT_proof` and `cartierSmooth_proof` inside). One field out, one LEAF in. -/

namespace HDec

namespace HSyn

/-- `OpenAddedLeaves25` with `kleimanPicZeroProper` replaced by Kleiman 9.5.4 as printed (kleiman-section2).
2 fields. -/
structure OpenAddedLeaves26 : Prop where
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). With the next three replaces `t09SymmIsogenyExists`. -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- kleiman-section2: for `X` projective, geometrically integral and geometrically normal over a field `K` with a
  `K`-point, the identity component of any scheme locally of finite type over `K` representing `Pic_{(X/K)(fppf)}`
  on locally Noetherian `K`-schemes is proper (Kleiman, *The Picard scheme*, Thm 9.5.4; locator UNVERIFIED). -/
  kleimanPicZeroProper954 : _root_.KleimanSection2.KleimanPicZeroProper954

/-- `OpenAddedLeaves22PZ` from `OpenAddedLeaves26`: `picZeroAbVar` (characteristic `0`) from Kleiman 9.5.4 and
the proved leaves. -/
theorem openAddedLeaves22PZ_of_OpenAddedLeaves26 (n : OpenAddedLeaves26) : OpenAddedLeaves22PZ where
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := _root_.KleimanSection2.picZeroAbVar0_of_954 n.kleimanPicZeroProper954

/-- **G0 with only the open leaves and the open glue** (kleiman-section2; hand fold). -/
theorem sixContactMin_of_open49 (r : OpenResearchLeaves31) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves26) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open45_pz r t (openAddedLeaves22PZ_of_OpenAddedLeaves26 l)

end HSyn

end HDec
