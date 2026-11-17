/-
Verification entry point for the exact fixed H-76 theorem.
This file reports the declaration kind, fully expanded statement and axioms.
It changes no definition and supplies no additional mathematical assumption.
-/
import ZInQKernel.Contrib.CloudW03NeronSurj.Main
import Lean

open Lean Elab Command Meta in
elab "#w03_neron_audit" : command => liftTermElabM do
  let proofName := `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof
  let propName := `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj
  let info ← getConstInfo proofName
  match info with
  | .thmInfo _ => logInfo m!"declaration kind: theorem; name: {proofName}"
  | _ => throwError "H-76 verification: expected a theorem declaration"
  let levels := info.levelParams.map Level.param
  let fixedType := mkConst propName levels
  unless ← isDefEq info.type fixedType do
    throwError "H-76 verification: theorem does not have the exact fixed Prop type"
  logInfo m!"exact fixed type: {info.type}"
  let expanded ← withTransparency .all <| whnf info.type
  logInfo m!"expanded fixed type: {expanded}"

set_option pp.universes true in
#w03_neron_audit

#print axioms ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof
