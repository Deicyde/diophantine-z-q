import ZInQKernel.Contrib.OneProof.RC.CMScope.Orientation

open ZInQ.Manuscript.RC.CMScope

#print axioms cmFieldOfDefinitionScoped_of_broad
#print axioms cmFieldOfDefinitionScoped_modelOne
#print axioms cmFieldOfDefinitionScoped_one

-- Construct the internal name so its numeric component is not parsed as source syntax.
open Lean Elab Command in
run_cmd do
  let lemmaName := mkPrivateNameCore `ZInQKernel.Contrib.OneProof.RC.CMScope.Orientation
    `ZInQ.Manuscript.RC.CMScope.orientation_of_form
  elabCommand (← `(#print axioms $(mkIdent lemmaName)))

#print axioms CMFieldOfDefinitionScoped.atForm
