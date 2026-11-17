import Research.DerivativeSwitch.ConjugateLocalTransport
import Research.DerivativeSwitch.ConjugateLocalH1
import Research.DerivativeSwitch.ActualBoundaryCup
import Research.DerivativeSwitch.OrthogonalComparison
import Lean.Util.CollectAxioms
set_option pp.universes true
set_option pp.explicit false
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print Research.DerivativeSwitch.ConjugateLocalTransport.twist
#print Research.DerivativeSwitch.ConjugateLocalTransport.conjugation
#print Research.DerivativeSwitch.ConjugateLocalTransport.IsCrossed
#print Research.DerivativeSwitch.ConjugateLocalTransport.LocalData
#print Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.transportUnit
#print Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.coordinates
#print Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.rawConjugate
#print Research.DerivativeSwitch.ConjugateLocalTransport.cocycleEvaluation
#print Research.DerivativeSwitch.ConjugateLocalTransport.h1Evaluation
#print Research.DerivativeSwitch.ConjugateLocalTransport.cocyclePullback
#print Research.DerivativeSwitch.ConjugateLocalTransport.h1Pullback
#print Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.h1Coordinates
#print Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.conjugateH1Coordinates
#print Research.DerivativeSwitch.ActualBoundaryCup.LocalCupData
#print Research.DerivativeSwitch.OrthogonalComparison.fibreD
#print Research.DerivativeSwitch.OrthogonalComparison.fibreComparison
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[`Research.DerivativeSwitch.ConjugateLocalTransport.crossed_conjugation, `Research.DerivativeSwitch.ConjugateLocalTransport.crossed_pow_of_trivial, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.tate_transporter, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.twist_transporter, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.twist_transporter_inv, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.tate_finite, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.twist_finite, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.twist_inertia, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.rawConjugate_isCrossed, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.conjugation_finite, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.conjugation_inertia, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.rawConjugate_finite, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.rawConjugate_inertia, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.coordinates_rawConjugate, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.coordinates_rawConjugate_of_neg_one, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.twist_conjugation_finite, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.twist_conjugation_inertia, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.coordinates_add_coboundary, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.conjugate_coordinates_add_coboundary, `Research.DerivativeSwitch.ConjugateLocalTransport.h1_projection_surjective, `Research.DerivativeSwitch.ConjugateLocalTransport.cocycleEvaluation_kills_kernel, `Research.DerivativeSwitch.ConjugateLocalTransport.h1Evaluation_projection, `Research.DerivativeSwitch.ConjugateLocalTransport.cocyclePullback_kills_kernel, `Research.DerivativeSwitch.ConjugateLocalTransport.h1Pullback_projection, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.h1Coordinates_projection, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.conjugateH1Coordinates_projection, `Research.DerivativeSwitch.ConjugateLocalTransport.LocalData.h1_local_transport, `Research.DerivativeSwitch.ActualBoundaryCup.closed_cup_differential, `Research.DerivativeSwitch.ActualBoundaryCup.pure_boundary_correction, `Research.DerivativeSwitch.ActualBoundaryCup.traced_pure_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_left_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_right_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_change_left, `Research.DerivativeSwitch.ActualBoundaryCup.traced_change_right, `Research.DerivativeSwitch.OrthogonalComparison.fibreComparison_commutes, `Research.DerivativeSwitch.OrthogonalComparison.fibreComparison_global, `Research.DerivativeSwitch.OrthogonalComparison.fibreComparison_sign_change, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_global_homotopy, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_global_homology, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_local_homotopy, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_local_homology]
  for name in names do
    let declaration ← getConstInfo name
    logInfo m!"STATEMENT {name}: {declaration.type}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  logInfo "AXIOM_AUDIT_PASS declarations=41"
