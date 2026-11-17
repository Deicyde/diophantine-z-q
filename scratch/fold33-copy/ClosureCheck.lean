import ZInQKernel.OneProof.Main
import Lean
/-! fold33-copy: the closure (types and values) of `ZInQ.OneProof.frozenTarget`, checked for the types of the
removed fields (homfree-noemb's pattern, scratch/homfree-noemb/ClosureCheck.lean). Prints `contains <name>: <bool>`
for each name; after the sga3-nbhd reroute the SGA 3 VI_B 3.10 names must be absent, after goodmodel-iso the GIT 6.14
names; `neronSchemeExtensionExists`'s type stays in the closure as a proved intermediate statement
(`neronSchemeExtensionExists_of_dedekind`), so the check for it is that no bundle field has it as type. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let names : List Name := [
    -- sga3-nbhd
    `CToPrinted.SGA3_VIB_3_10, `SGA3IdComp.SGA3_VIB_3_10_Nbhd, `SGA3IdComp.sga3_VIB_3_10_of_nbhd,
    `CToPrinted.idComp_baseChange, `CToPrinted.semistableNeronBaseChange_of_printed_full,
    `SGA3Nbhd.semistableNeronBaseChange_noSGA3,
    -- goodmodel-iso
    `DictModels.MumfordConn.MumfordGroupLawConn, `DictModels.MumfordConn.mumfordGroupLaw_of_conn,
    `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw,
    `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind, `ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind,
    `ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind,
    `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists,
    -- earlier folds of leaf-fold33 (must stay absent)
    `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite, `sorryAx,
    -- fold33-copy: the originals are bypassed, the copies used
    `HDec.HSyn.OpenResearchLeaves14, `HDec.HSyn.OpenResearchLeaves29, `HDec.HSyn.sixContactMin_of_open41,
    `HDec.HSyn.OpenResearchLeaves29NS, `HDec.HSyn.sixContactMin_of_open42,
    `HDec.HSyn.OpenResearchLeaves29GM, `HDec.HSyn.sixContactMin_of_open43]
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
  IO.println s!"frozenTarget: closure {seen.size}"
  for b in names do
    IO.println s!"  contains {b}: {seen.contains b}"
  -- the bundle binders of frozenTarget and their fields
  if let some ci := env.find? `ZInQ.OneProof.frozenTarget then
    let bs := ci.type.getUsedConstants.filter fun n =>
      (isStructure env n) && (n.toString.startsWith "HDec.HSyn.Open")
    for b in bs do
      let fs := getStructureFields env b
      IO.println s!"  bundle {b}: {fs.size} fields"
      for f in fs do
        if let some p := env.find? (b ++ f) then
          let t := p.type.getForallBody
          if t.getUsedConstants.any (fun n => names.contains n) then
            IO.println s!"    field {f} has a checked type: {t.getUsedConstants.toList.filter (names.contains ·)}"
