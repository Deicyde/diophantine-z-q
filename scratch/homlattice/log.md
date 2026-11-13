# homlattice results log

## Step 1 (12:10): glue, `scratch/homlattice/HomLattice.lean` (imports ZInQKernel.Contrib.HomUnify.Corr)
- `lake build ZInQKernel.Contrib.HomUnify.Corr`: OK (9064 jobs), VERIFIED.
- `lake env lean scratch/homlattice/HomLattice.lean`: exit 0, ~5 s; all `#print axioms`
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- Proved: isUniformization_iff, cEvalAt_comp, isAnalyticHom_comp (algebraic hom preserves
  analyticity), isAnalyticHom_lin (Φ∘M analytic), homLinearLift_of_analyticHomLift,
  homRealize_of_analyticHomAlgebraic, homLatticeCorr_of_analytic, t11a_riemannEnd_of_analytic,
  t11aHom_of_analytic.
- New Props: IsAnalyticHom (IsUniformization minus kernel/surjectivity), AnalyticHomLift,
  UnifLocalInverse, AnalyticHomAlgebraic.
