import ZInQKernel.OneProof.H.TailX
import ZInQKernel.Contrib.OneProof.STQM

/-! st-qbar: the replacement term for the only consumer of `shimuraTaniyamaQbar` (TailX.lean L261,
`stQM := stQM_lf7 l.shimuraTaniyamaQbar` in `addedLeaves6_of_open7`), checked in the same context. -/

namespace HDec.HSyn

/-- The replacement term at TailX L261 (no use of `l.shimuraTaniyamaQbar`). -/
theorem stQM_st (r : OpenResearchLeaves7) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7) :
    G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM :=
  _root_.GapST.stQM_of r.r1r2 l.y3Connected (qmRows_of7 t l).2.1
    (_root_.AvSplit.Final.h25 t.mumfordTorsionAlgClosed)
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
    (_root_.AvSplit.Final.h69 t.uniformizationLeafAll t.gagaMorphism)

/-- `addedLeaves6_of_open7` with `stQM` filled by `stQM_st` (verbatim otherwise, TailX L245-L268). -/
theorem addedLeaves6_of_open7_st (r : OpenResearchLeaves7) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7) :
    OpenAddedLeaves6 where
  cmOptimalEmbedding := (qmRows_of7 t l).2.2
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodulBase3 := l.qmHauptmodulBase3
  qmClassNumberOne := QMSplit.CNO.qmClassNumberOne_proof
  senTwist := HodgeLF7.senTwist (_root_.ZInQ.Contrib.HodgeSplit.senTwist_of_tate l.tateTwistInvariants l.axSenTate)
  finiteImageHT :=
    HodgeLF7.finiteImageHT (_root_.ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate l.tateTwistInvariants l.axSenTate)
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := isogenyQuasiInverse_lf7 l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := (qmRows_of7 t l).1
  alFixedPoints := (qmRows_of7 t l).2.1
  zariskiConnectedness := l.zariskiConnectedness
  stQM := stQM_st r t l
  valenceFormulaGammaStar := l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
  shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (LeafAdopt.R1R2fp_of_rep r.r1r2)
    l.shimuraGoodReductionNoGuard
  curveBijIso := curveBijIso_lf7

end HDec.HSyn

#print axioms HDec.HSyn.addedLeaves6_of_open7_st
