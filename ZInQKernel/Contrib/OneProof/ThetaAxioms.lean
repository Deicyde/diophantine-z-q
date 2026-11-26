import ZInQKernel.Contrib.OneProof.ThetaSeriesConvergence
import ZInQKernel.Contrib.OneProof.ThetaLineBundle
import ZInQKernel.Contrib.OneProof.ThetaLineAnalytic
import ZInQKernel.Contrib.OneProof.ThetaFourier

/-! # Axiom check for the theta line

`#print axioms` for the headline theorems of `ThetaSeriesConvergence`, `ThetaLineBundle`,
`ThetaLineAnalytic` and `ThetaFourier`, so that the hosted check records their axioms.
-/

#print axioms BPAnalytic.analyticAt_riemannTheta
#print axioms BPAnalytic.ThetaLine.factor_cocycle
#print axioms BPAnalytic.ThetaLine.contMDiff_bundleThetaSection
#print axioms BPAnalytic.exists_riemannTheta_add_real_ne_zero
#print axioms BPAnalytic.riemannTheta_not_eventually_zero
