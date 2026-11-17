import ZInQKernel.Contrib.OneProof.HodgeTatePairingCore0
import ZInQKernel.Contrib.OneProof.AxSenTate
import ZInQKernel.Contrib.OneProof.TateTwistInvariants
import ZInQKernel.Contrib.OneProof.MilneIsogenyQuasiInverse
import ZInQKernel.Contrib.OneProof.PhiSurjCharZero
import ZInQKernel.Contrib.OneProof.PicLocFinType
import ZInQKernel.Contrib.OneProof.IdentityComponentLFT
import ZInQKernel.OneProof.H.TailZ24

/-!
# `HodgeSplit.HodgeTateDecompAbVar` from a dimension-free printed leaf, over the fold33 base

Task fold34-ht (2026-11-16; report `docs/research/fold34-ht.md`). hodgetate-from-dr
(`HodgeTatePairing.lean`, `hodgeTateDecompAbVar_of_printed`) proved the open field `hodgeTateDecompAbVar` from the
new leaf `HodgeTateDecompExists` and the T9 leaves of leaf-fold32b (`picZeroAbVar`, `mumfordKLFiniteSectionAC`,
`mumfordPhiSurjectiveAC`, `weilPairingMumford`). On the fold33 base these are proved or gone: phisurj proved the
Weil pairing and `φ_L` an isogeny from `picRepresentableAbVar`, `picZeroAbVar` and T5, and piczero-char0 replaced
`picZeroAbVar` by its characteristic-`0` form `PicZeroAbVar0`, proved from `picLocFinType` (proved, piclft),
`identityComponentLFT` (proved, idcomp-lft) and `kleimanPicZeroProper` (open). The base field of the Hodge–Tate field
is finite over `ℚ_p`, hence of characteristic `0`, so the characteristic-`0` T9 (`T09_SymmIsogenyExists0`) suffices
(`hodgeTateDecompAbVar_of_leaves0`). The open inputs are the new leaf, `picRepresentableAbVar`,
`kleimanPicZeroProper` (added leaves) and `mumfordTorsionAlgClosed` (T5, textbook).
-/

namespace ZInQ.Contrib.HodgeTateFromPairing

/-- **T9 in characteristic `0` from the open fields of the fold33 base**: `PicRepresentableAbVar`,
`KleimanPicZeroProper` and T5 (`MumfordTorsionAlgClosed`), through piczero-char0's `picZeroAbVar0_of_leaves` (with
piclft's and idcomp-lft's proofs) and phisurj's characteristic-`0` theorems. -/
theorem t09SymmIsogenyExists0_of_open (h1 : _root_.T09Pic.PicRepresentableAbVar)
    (hK : _root_.PicFix.KleimanPicZeroProper) (hM : _root_.AvSplit.MumfordTorsionAlgClosed) :
    _root_.PicZeroChar0.T09_SymmIsogenyExists0 :=
  have h2 : _root_.PicZeroChar0.PicZeroAbVar0 :=
    _root_.PicZeroChar0.picZeroAbVar0_of_leaves _root_.PicLFT.picLocFinType_proof
      _root_.IdCompLFT.identityComponentLFT_proof hK
  _root_.PhiSurj.t09SymmIsogenyExists0_of_four0 h1 h2 (_root_.PhiSurj.phiAmpleIsogeny0_of_open h1 h2 hM)
    (_root_.PhiSurj.weilPairingMumford0_of_open h1 h2 hM)

/-- **`HodgeTateDecompAbVar` from the leaf `HodgeTateDecompExists` and open fields of the fold33 base**: T5
(`AvSplit.MumfordTorsionAlgClosed`), `T09Pic.PicRepresentableAbVar` and `PicFix.KleimanPicZeroProper`. Tate's two
theorems, Ax–Sen–Tate, the isogeny quasi-inverse, `PicLocFinType` and `IdentityComponentLFT` are theorems
(contributions). -/
theorem hodgeTateDecompAbVar_of_open (hHT : HodgeTateDecompExists)
    (hM : _root_.AvSplit.MumfordTorsionAlgClosed) (h1 : _root_.T09Pic.PicRepresentableAbVar)
    (hK : _root_.PicFix.KleimanPicZeroProper) :
    ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar :=
  hodgeTateDecompAbVar_of_leaves0 hHT ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof
    (t09SymmIsogenyExists0_of_open h1 hK hM)
    (HDec.HSyn.isogenyQuasiInverse_lf7 ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof)
    (_root_.AvSplit.Final.h25 hM)

end ZInQ.Contrib.HodgeTateFromPairing

#print axioms ZInQ.Contrib.HodgeTateFromPairing.t09SymmIsogenyExists0_of_open
#print axioms ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_open
