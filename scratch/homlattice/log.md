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

## Step 2 (12:25): pure analysis + lifting
- Proved `eq_fderiv_of_locally_additive` (F additive on ball(0,r), ℂ-differentiable at 0 ⇒
  F = fderiv F 0 on the ball), `analyticHomLift_of_unifLocalInverse`,
  `homLinearLift_of_unifLocalInverse`, `homLatticeCorr_of_local`.
- `lake env lean scratch/homlattice/HomLattice.lean`: exit 0; 13 `#print axioms` reports, all
  [propext, Classical.choice, Quot.sound]; no sorry, no error (out_HomLattice.txt). VERIFIED.

## Step 3 (12:45): converse for realization; rigidity copy; GAGA for morphisms
- `analyticHomAlgebraic_of_homRealize` (HomRealize + AnalyticHomLift + UniformizationExists +
  dimension finiteness ⇒ AnalyticHomAlgebraic), `t11a_riemannEnd_of_local`,
  `homLatticeCorr_of_local_realize`.
- Copied `MulRigidity` (scratch/alg-frob-red/src_Rigidity.lean lines 18-183, verbatim, by script
  with boundary asserts) into HomLattice.lean. New: `AnalyticMapAlgebraic` (conclusion a mere
  morphism), `eta_comp_of_one_comp`, `analyticHomAlgebraic_of_map` (rigidity),
  `analyticMapAlgebraic_iff`, `homLatticeCorr_of_local_map`, `t11a_riemannEnd_of_local_map`.
- `lake env lean scratch/homlattice/HomLattice.lean`: exit 0 in 10 s; 22 `#print axioms`, all
  [propext, Classical.choice, Quot.sound]; no sorry/error. VERIFIED.
