import ZInQKernel.Contrib.OneProof.ColmezTiltIso.Action
import ZInQKernel.Contrib.OneProof.ColmezTiltIso.RowTp

/-!
# Axiom evidence for `ColmezTiltIso`

`#print axioms` for the main declarations; the build log shows the output. Each should list only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- The ring isomorphism and the printed addition.
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezEquiv
#print axioms ZInQ.Contrib.ColmezTiltIso.ColmezR.add_seq_isPAdicLim
-- `θ`.
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezTheta
#print axioms ZInQ.Contrib.ColmezTiltIso.eq_colmezTheta_of_printed
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezTheta_teichmuller
#print axioms ZInQ.Contrib.ColmezTiltIso.thetaPlusCp_ofPlus_wittEquiv
-- `B_dR^+` and `B_dR`.
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezBdRPlusEquiv
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezBdREquiv
#print axioms ZInQ.Contrib.ColmezTiltIso.isDiscreteValuationRing_colmezBdRPlus
#print axioms ZInQ.Contrib.ColmezTiltIso.ker_colmezThetaPlus
-- The Galois action.
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezEquiv_galAct
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezBdRPlusAct
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezBdRAct
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezBdRPlusEquiv_act
#print axioms ZInQ.Contrib.ColmezTiltIso.colmezBdREquiv_act
-- The row on `T_p`.
#print axioms ZInQ.Contrib.ColmezTiltIso.Tp.shapeT_iff_shapeV
#print axioms DeRhamScholze.TatePrints.ColmezTp.colmez1992DeRhamAbVarTp_iff_cp
#print axioms DeRhamScholze.TatePrints.ColmezTp.colmez1992DeRhamAbVar_iff_tp
