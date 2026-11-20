import Lean
import ZInQKernel.Contrib.OneProof.RC.PMWire.Assembly
import ZInQKernel.Contrib.OneProof.RC.PMQuotient.Assembly
import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves

/-! Focused variant of the discharge audit: check the dependent
`PreLeaves.odd_staged` field at the constructor's very same `W`.
List all of its binders, including data and typeclass inputs. -/

open Lean Elab Command Meta
open ZInQ.Manuscript.RC

elab "#discharges" : command => liftTermElabM do
  let c ← getConstInfo ``PMWire.oddStagedOfGoodRows
  let prior ← getConstInfo ``PMQuotient.oddStagedOfGoodRows
  let oldCount ← forallTelescope prior.type fun ys _ => pure ys.size
  forallTelescope c.type fun xs goal => do
    let_expr Nonempty I := goal | throwError "expected the staged point and theta instance"
    let W := I.getAppArgs.back!
    let pre ← mkAppM ``Wiring.PreLeaves #[W]
    withLocalDeclD `pre pre fun p => do
      let projection ← mkAppM ``Wiring.PreLeaves.odd_staged #[p]
      unless ← isDefEq (← inferType projection) goal do
        throwError "the constructor does not fill PreLeaves.odd_staged"
    logInfo m!"DISCHARGES Wiring.PreLeaves.odd_staged at {W}"
    logInfo m!"  binders: {xs.size} (PMQuotient: {oldCount})"
    for x in xs do
      let d ← x.fvarId!.getDecl
      logInfo m!"  {d.userName} : {d.type}"
    let axioms := (← collectAxioms c.name).toList
    for a in axioms do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "unexpected axiom: {a}"
    logInfo m!"  axioms: {axioms}"

#discharges
