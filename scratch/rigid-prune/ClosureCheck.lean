import ZInQKernel.OneProof.Main
import Lean
/-! rigid-prune: which rigidity constants are in `frozenTarget`'s closure. -/
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
  for n in [`LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core, `LeafQM.AV.R1UnivRigid.MumfordRigidity,
      `LeafQM.AV.R1UnivRigid.exists_qmAbScheme, `LeafQM.AV.R1UnivRigid.r1univProps_of_ab,
      `LeafQM.AV.R1UnivRigid.r1fpProps_eq_ab', `LeafQM.AV.R1UnivRigid.MumfordRigidityCore,
      `LeafQM.AV.R1UnivRigid.QMFamilyGroupLaw, `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_core,
      `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, `ZInQ.Contrib.MumfordRigidity.mumfordGroupLaw_of_core,
      `HDec.HSyn.mumfordRigidity_of14] do
    logInfo m!"{n}: {if seen.contains n then "IN closure" else "not in closure"}"
