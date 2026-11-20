import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.Suppliers

open ZInQ.Contrib.RC53Assist.Calibration

#print axioms LocalUnramifiedTorsion
#print axioms ActiveLocalAction
#print axioms localTateMatrix
#print axioms MovingLocalAction.mk
#print axioms locH0EquivFixed
#print axioms ecurve_torsTwo_fixed
#print axioms active_fixed_iff_two_smul
#print axioms centralCoordinates
#print axioms det_signed_frobenius_sub_one
#print axioms card_locH0_moving
#print axioms card_locH0_active
#print axioms GenuineLengthBlockModelP.mk
#print axioms GenuineLengthBlockModelP.toLengthModel
#print axioms CalibrationModelHKL2P.mk
#print axioms CalibrationModelHKL2P.toHKL2
#print axioms CalibrationInputsHKL2P
#print axioms calibrationInputsHKL2_of_HKL2P
#print axioms calibrationTarget_of_HKL2P
#print axioms localUnramifiedTorsion_of_goodReduction
#print axioms activeLocalAction_of_goodReduction
#print axioms activeLocalAction_of_split_squarefree
#print axioms movingPrime_absNorm_of_two_places
#print axioms moving_isFrobAt_of_residueDegreeOne
#print axioms localQuadChar_of_isFrobAt
#print axioms movingLocalAction_of_frobeniusTrace
#print axioms MovingPrimeData.localAction

open Lean Elab Command in
elab "#audit_local_private " file:ident ident:ident : command => do
  let moduleName := `ZInQKernel.Contrib.OneProof.RC.CalLocalLengths ++ file.getId
  let privPrefix := Name.num (`_private ++ moduleName) 0
  let name := privPrefix ++ `ZInQ.Contrib.RC53Assist.Calibration ++ ident.getId
  elabCommand (← `(command| #print axioms $(mkIdent name)))

#audit_local_private LocalOrders centralChar_coe
#audit_local_private LocalOrders central_tmul_smul
#audit_local_private LocalOrders central_smul_of_torsion_fixed
#audit_local_private LocalOrders torsionFixed_of_two_smul
#audit_local_private LocalOrders centralCoordinates_smul
#audit_local_private LocalOrders fixed_iff_frobenius
#audit_local_private Suppliers prime_under_of_above
#audit_local_private Suppliers ncard_primesOver_eq_of_two_places
