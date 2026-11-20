import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.KolyvWeil.PoleCompleteness

#check @ZInQ.OneProof.frozenTarget
#print axioms ZInQ.OneProof.frozenTarget
#print axioms ZInQ.Manuscript.KolyvWeil.kolyvaginThm1_of_prints
#print axioms ZInQ.Manuscript.KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print

#discharges

open Lean Elab Command Meta ZInQ.OneProof.Discharges in
run_cmd do
  let env ← getEnv
  let hyps ← liftTermElabM openHyps
  logInfo m!"OPEN-LABELS {(toJson (hyps.map (·.label))).compress}"
  for h in hyps do
    if ["hB", "hK", "hB6", "hKPrint"].contains h.label then
      let pp ← liftTermElabM do
        pure (toString (← ppExpr h.type))
      let full ← liftTermElabM do
        withOptions (·.setBool `pp.fullNames true) do
          pure (toString (← ppExpr h.type))
      let doc ← match h.type.getAppFn with
        | .const c _ => pure ((← findDocString? env c).getD "")
        | _ => pure ""
      let entry := Json.mkObj [
        ("field", toJson h.label), ("bundle", toJson "frozenTarget"),
        ("statement", toJson pp), ("type", toJson full), ("docstring", toJson doc)]
      logInfo m!"RANK-ENTRY {entry.compress}"
