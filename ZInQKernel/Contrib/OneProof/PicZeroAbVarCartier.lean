import ZInQKernel.Contrib.OneProof.PicZeroSmoothCartier
import ZInQKernel.Contrib.OneProof.CartierSmooth

/-!
# `PicZeroAbVar` with Cartier's theorem proved (pic-smooth)

`PicZeroSmoothCartier.lean` with `AVGlue.CartierSmooth` supplied by
`ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof`:
* `PicSmooth.picZeroAbVar_of_printed2 : PicLocFinType → IdentityComponentLFT → PicZeroSmoothPosChar →
  KleimanPicZeroProper → PicZeroAbVar`;
* `PicSmooth.picZeroAbVarAt_charZero`: `PicZeroAbVar` at every field of characteristic `0` from the three LEAF
  statements `PicLocFinType`, `IdentityComponentLFT`, `KleimanPicZeroProper` alone.
-/

namespace PicSmooth

open T09Pic PkgI3 PicDict PicFix

/-- **`PicZeroAbVar` at every field of characteristic `0` from the three LEAF statements alone** (Cartier's
theorem is `cartierSmooth_proof`). -/
theorem picZeroAbVarAt_charZero (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3b : KleimanPicZeroProper)
    (K : Type) [Field K] [CharZero K] : PicZeroAbVarAt K :=
  picZeroAbVarAt_charZero_of_cartier ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof h1 h2 h3b K

/-- **Main result (`PicZeroAbVar`)**, Cartier's theorem supplied by `cartierSmooth_proof`: from the three LEAF
statements and `PicZeroSmoothPosChar` (pending reading). -/
theorem picZeroAbVar_of_printed2 (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (hp : PicZeroSmoothPosChar) (h3b : KleimanPicZeroProper) : PicZeroAbVar :=
  picZeroAbVar_of_cartier h1 h2 ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof hp h3b

end PicSmooth
