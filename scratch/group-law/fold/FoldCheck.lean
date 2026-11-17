import ZInQKernel.OneProof.Main
import Lean
open Lean

#check @HDec.HSyn.OpenResearchLeaves26.mumfordGroupLaw
#print axioms ZInQ.OneProof.frozenTarget

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
  for n in [`ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, `ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR,
      `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw, `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr,
      `ZInQ.Contrib.GroupLaw.MumfordGroupLawLocal] do
    logInfo m!"{n}: {if seen.contains n then "IN closure" else "not in closure"}"
