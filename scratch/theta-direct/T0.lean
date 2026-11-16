import ZInQKernel.Contrib.OneProof.ThetaDirect.Printed
import ZInQKernel.Contrib.OneProof.ValenceCocompact
import ZInQKernel.Contrib.OneProof.GammaStarArea

open Polynomial
local notation "𝔸" => algebraicClosure ℚ ℂ

#check @ValenceCocompact.valenceFormulaCocompactEq_proof
#check @HDec.GammaStarArea.shimizuCovolumeO1_proof
#check @HDec.LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves
#check @HDec.LeafQCheck.VB.ellipticOrderLe6_proof
#check @HDec.LeafQCheck.HM.QMSplit.ellipticOrderDvd_proof
#check @analyticOrderAt_eq_top
#check @AnalyticAt.analyticOrderAt_eq_zero
#check @AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
#check @HDec.HSyn.G0Split.FibreQM.PeriodMap.omegaSiegel_proof
#check @HDec.LeafQCheck.HM.QMSplit.Value24.omega_tau24
#check @HDec.LeafQCheck.HM.QMSplit.Value24.tau24
#check @CM24.mpoly_theta
#check @HDec.LeafQCheck.HM.jNum_tau4
#check @HDec.LeafQCheck.HM.Sf_tau4
#check @HDec.LeafQCheck.HM.QMSplit.auto8
#check @HDec.LeafQCheck.HM.QMSplit.zero_iff
#check @GapTheta.thetaModularity_proof
#check @HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.igusaAlg_all
#check @HDec.HSyn.G0Split.ThetaPt.ThetaGlue.igusaThetaSymmetric_of_alg
#check @HDec.HSyn.G0Split.ThetaPt.ThetaGlue.thetaEightSquare
#check @HDec.LeafQCheck.gammaStarGen_proof
#check @HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaConst_odd
#check @HDec.HSyn.G0Split.ThetaPt.ThetaSplit.thetaConst_eq_pkgI1

example (a b : ℂ) (ha : a ∈ 𝔸) (hb : b ∈ 𝔸) : (-8/27 : ℂ) * a ^ 3 + 1081344 * b - a * b ∈ 𝔸 := by
  apply_rules [add_mem, sub_mem, mul_mem, pow_mem, div_mem, neg_mem, one_mem, natCast_mem, ofNat_mem]

example (q : ℚ) : (q : ℂ) ∈ 𝔸 := by exact?
example (x : ℂ) (h : x ^ 2 ∈ 𝔸) : x ∈ 𝔸 := by
  rw [mem_algebraicClosure_iff] at *
  exact IsAlgebraic.of_pow (by norm_num) h
