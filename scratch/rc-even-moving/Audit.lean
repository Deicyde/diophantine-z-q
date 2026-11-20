import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Assembly
import Lean.Elab.Print

open ZInQ.Manuscript.RC.EvenMoving


-- Affine.lean
#print axioms affinePoint_coe
#print axioms affinePoint_holo
#print axioms affinePoint_cusps

-- Assembly.lean
#print axioms movingStep
#print axioms evenMovingSieve
#print axioms evenWeightTwo_from_unary
#print axioms evenExpansion_from_unary

-- Character.lean
#print axioms kronecker_of_odd
#print axioms primeCharacter_nat
#print axioms primeCharacter_neg_one
#print axioms primeCharacter_sq

-- Dilation.lean
#print axioms Vp_eq_scale
#print axioms unitCharacter_d
#print axioms Vp_threeHalves

-- Matrices.lean
#print axioms det_eq
#print axioms sl_coord
#print axioms mem_level_iff
#print axioms scalePoint_coe
#print axioms scaleLower_entries
#print axioms scale_smul
#print axioms rightT_entries
#print axioms leftT_entries

-- PrimeGauss.lean
#print axioms quadraticFourier_prime_scale
#print axioms theta_right_cusp

-- Theta.lean
#print axioms thetaMultiplier_rightT
#print axioms thetaMultiplier_leftT
#print axioms thetaMultiplier_triangular
#print axioms thetaMultiplier_scale

-- Translate.lean
#print axioms unscalePoint_coe
#print axioms Up_eq_affine
#print axioms upSquare_terms
#print axioms Up_cusps
#print axioms Up_holo
#print axioms upSquare_threeHalves

-- Ask the same builtin command to audit the private proof helpers.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, c) =>
    match c, privateToUserName? n with
    | .thmInfo _, some m =>
      if (`ZInQ.Manuscript.RC.EvenMoving).isPrefixOf m then some n else none
    | _, _ => none
  for n in names.mergeSort Name.lt do
    elabCommand (← `(#print axioms $(mkIdent n)))
