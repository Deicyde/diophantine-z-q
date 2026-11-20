import ZInQKernel.Contrib.OneProof.RC.KatoP2.RealSignBridge
import Lean.Elab.Print

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.KatoP2

open Lean Elab Command in
run_cmd do
  for name in #[`realConj_sq, `realConj_tate_det, `finrank_ker_add_one_of_involution] do
    let decl := Name.num `_private.ZInQKernel.Contrib.OneProof.RC.KatoP2.RealSign 0 ++
      `ZInQ.Manuscript.RC.KatoP2 ++ name
    elabCommand (← `(command| #print axioms $(mkIdent decl)))

#print axioms rationalTwist_realSigns
#print axioms Checked.KodaiConstituent.ofArithmetic

open Lean Elab Command in
run_cmd do
  if (← getEnv).header.moduleNames.contains `ZInQKernel.OneProof.Main then
    throwError "The real sign bridge imports the frozen main module"
  logInfo "The real sign bridge does not import the frozen main module."
