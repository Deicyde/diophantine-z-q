import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.JDescent2
import ZInQKernel.Contrib.OneProof.JDescent3FunctionField

/-! Row-only input to the standard scanner. The type of `OpenResearchLeaves66.cmjDegree`
is copied from the live declaration in `ZInQKernel/OneProof/H/TailZ92.lean`.
This scratch definition merely gives the scanner its input without importing the full entry
point. It has no mathematical conclusion and is not the live theorem. -/

set_option linter.unusedVariables false in
def ZInQ.OneProof.frozenTarget (cmjDegree : _root_.HDec.CMBranch.CMjDegree) : Unit := ()

#discharges
