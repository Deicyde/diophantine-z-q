import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.NeronGoodModelIso
import Lean
/-! goodmodel-iso fold check: run with the overlay of fold G first on LEAN_PATH
(scratch/goodmodel-iso/fold/compile_overlay.sh /tmp/gmifold/G). -/
open Lean

#check @ZInQ.OneProof.frozenTarget
#check @HDec.HSyn.sixContactMin_of_open39
#print HDec.HSyn.OpenResearchLeaves28
#print HDec.HSyn.OpenTextbookLeaves14
#print axioms ZInQ.OneProof.frozenTarget
#print axioms HDec.HSyn.sixContactMin_of_open39

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
      `ZInQ.Contrib.GroupLawNeron.mumfordGroupLawDVR_of_neron, `ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind,
      `ZInQ.Contrib.GoodModelIso.neronGoodModelIso_of_dvr,
      `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists,
      `ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind] do
    logInfo m!"{n}: {if seen.contains n then "IN closure" else "not in closure"}"

-- the open hypotheses of the folded `frozenTarget` (and which of them the contributions discharge)
#discharges
