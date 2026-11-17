import ZInQKernel.OneProof.Main
import Lean
/-! group-law-dvr fold check: run with the overlay of a fold variant first on LEAN_PATH
(scratch/group-law-dvr/fold/compile_overlay.sh). -/
open Lean

#check @HDec.HSyn.OpenResearchLeaves27.mumfordGroupLaw
#check @HDec.HSyn.sixContactMin_of_open38
#print HDec.HSyn.OpenResearchLeaves28
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
  for n in [`DictModels.MumfordConn.MumfordGroupLawConn, `DictModels.MumfordConn.mumfordGroupLaw_of_conn,
      `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw,
      `ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR, `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr,
      `ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso, `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind,
      `ZInQ.Contrib.GroupLawNeron.mumfordGroupLawDVR_of_neron] do
    logInfo m!"{n}: {if seen.contains n then "IN closure" else "not in closure"}"
