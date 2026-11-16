import ZInQKernel.OneProof.H.TailO
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
set_option pp.fullNames true
example (A : PkgI3.AbVar ℂ) : ZInQ.LeafPush2.CPts A (RingHom.id ℂ) = PkgI3.AbVar.Pt ℂ A := rfl
#check @MonObj.comp_pow
#check @MonObj.pow_comp
#check @HDec.G0ModField.transportLevel
#check @HDec.G0ModField.transportIso
#print HDec.HomUnify.HomLatticeCorr
#check @HDec.LeafQM.AV.Pin.Exact.conjO_apply
#check @HDec.LeafQM.AV.Pin.Exact.tt
#check @PkgI3.AbVar.dim_finite
#check @HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.bc_isPullback
#check @HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral
#check @HDec.PeriodGlue.eta_comp
#check @HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.eta_bc_fst
#check @HDec.LeafQM.AV.Pin.NormO.ui
example : (HDec.LeafQM.AV.Pin.Exact.tt 1 : LeafQM.B) = (LeafQM.AV.oi : LeafQM.B) := rfl
example : (HDec.LeafQM.AV.Pin.Exact.tt 2 : LeafQM.B) = (LeafQM.AV.oj : LeafQM.B) := rfl
example : (HDec.LeafQM.AV.Pin.Exact.tt 3 : LeafQM.B) = ((LeafQM.AV.oi * LeafQM.AV.oj : LeafQM.O) : LeafQM.B) := rfl
