import ZInQKernel.Contrib.OneProof.RC.O7Character.Character
import ZInQKernel.Contrib.OneProof.RC.O7Character.Stage
import Lean

open Lean Elab Command
open ZInQ.Manuscript.RC.O7Character

#print axioms quadraticBasis
#print axioms normCharacterDescent
#print axioms StageIntegralArithmetic
#print axioms stageIntegralArithmetic

run_cmd do
  let basis := `ZInQKernel.Contrib.OneProof.RC.O7Character.Basis
  let character := `ZInQKernel.Contrib.OneProof.RC.O7Character.Character
  for (moduleName, decl) in [
    (basis, `ZInQ.Manuscript.RC.O7Character.half_discr),
    (basis, `ZInQ.Manuscript.RC.O7Character.spans_of_discr),
    (basis, `ZInQ.Manuscript.RC.O7Character.quadraticBasisOfDiscr),
    (character, `ZInQ.Manuscript.RC.O7Character.principal_norm_formula),
    (character, `ZInQ.Manuscript.RC.O7Character.chiD_principal),
    (character, `ZInQ.Manuscript.RC.O7Character.exists_picClass_coprime)] do
    let id := mkIdent (mkPrivateNameCore moduleName decl)
    elabCommand (← `(#print axioms $id:ident))
