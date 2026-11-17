import ZInQKernel.OneProof.H.TailZ48
import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZero
open HDec.HSyn
set_option maxHeartbeats 400000 in
example (l : OpenAddedLeaves19) : ZInQ.Contrib.AVB1.PoincareComplement :=
  _root_.PicZeroChar0.Poincare.poincareComplement_of_open0 l.picRepresentableAbVar
    (PicZeroChar0.picZeroAbVar0_of_picZeroAbVar l.picZeroAbVar)
    (_root_.PicZeroChar0.phiAmpleIsogeny0_of_printed (PicZeroChar0.mumfordKLFiniteSectionAC0_of l.mumfordKLFiniteSectionAC) l.mumfordPhiSurjectiveAC)
    _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof _root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
example (h : PicZeroChar0.PicZeroAbVar0) (h1 : T09Pic.PicRepresentableAbVar) (h2 : PicZeroChar0.PhiAmpleIsogeny0) : ZInQ.Contrib.AVB1.PoincareComplement :=
  _root_.PicZeroChar0.Poincare.poincareComplement_of_open0 h1 h h2
    _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof _root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
#check @PicZeroChar0.Poincare.poincareComplement_of_open0
