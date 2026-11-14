import ZInQKernel.OneProof.Main
/-! op-dedupe: the fields of frozenTarget's hypothesis structures, with their types (after the dedupe). -/
open Lean Meta Elab Command
elab "#opd_fields " id:ident : command => liftTermElabM do
  let env ← getEnv
  let n := id.getId
  let some info := getStructureInfo? env n | throwError "not a structure"
  for f in info.fieldNames do
    let pn := n ++ f
    let some ci := env.find? pn | continue
    let t ← forallTelescope ci.type fun _ b => pure b
    let t ← instantiateMVars t
    IO.println s!"{n}\t{f}\t{(← ppExpr t).pretty 100000}"
#opd_fields HDec.HSyn.OpenResearchLeaves2
#opd_fields HDec.HSyn.OpenTextbookLeaves4
#opd_fields HDec.HSyn.OpenAddedLeaves4
#opd_fields HDec.HSyn.OpenGlue4
