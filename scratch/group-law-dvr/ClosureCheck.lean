import ZInQKernel.OneProof.Main
import Lean
/-! group-law-dvr: on the merged tree (origin/main c1e4ed1b), who in `frozenTarget`'s closure uses the
group-law leaves. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
  let targets : List Name := [`DictModels.MumfordConn.MumfordGroupLawConn,
      `DictModels.MumfordConn.mumfordGroupLaw_of_conn,
      `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw,
      `LeafQM.AV.R1UnivRigid.QMFamilyGroupLaw, `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw,
      `ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR, `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists]
  for n in targets do
    logInfo m!"{n}: {if seen.contains n then "IN closure" else "not in closure"}"
  for c in seen.toList do
    if let some ci := env.find? c then
      let used := ci.type.getUsedConstants ++ ((ccValue? ci).map (·.getUsedConstants)).getD #[]
      let hits := targets.filter (fun t => used.contains t)
      if !hits.isEmpty && !targets.contains c then
        logInfo m!"USER {c} uses {hits}"
