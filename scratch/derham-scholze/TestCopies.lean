import ZInQKernel.Contrib.OneProof.PanBergerPst
import ZInQKernel.Contrib.OneProof.BdRInvariants

variable (p : ℕ) [Fact p.Prime]

example (σ : ZInQ.Contrib.G9.PkgI4.GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    HDec.PkgI4.DR.bdrPlusMap p (HDec.PkgI4.oAct p σ) y =
      ZInQ.Contrib.G9.PkgI4.DR.bdrPlusMap p (ZInQ.Contrib.G9.PkgI4.oAct p σ) y := rfl

example (σ : ZInQ.Contrib.G9.PkgI4.GQp p) (i : ℤ) :
    HDec.PkgI4.cycPow p σ i = ZInQ.Contrib.G9.PkgI4.cycPow p σ i := rfl

example (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    HDec.PkgI4.BergerBst.toBdR p y = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (ZInQ.Contrib.G9.PkgI4.BdR p) y := rfl

example (a : ℤ_[p]) : HDec.PkgI4.BmaxOne.zpB p a = ZInQ.Contrib.G9.qpToPlus p (a : ℚ_[p]) := by
  apply BdRInv.alg_injective p
  have := HDec.PkgI4.BmaxOne.toBdR_zpB p a
  exact this
