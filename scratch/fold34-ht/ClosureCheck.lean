import ZInQKernel.OneProof.Main
import Lean
/-! fold34-ht (from fold33-pic, from fold33-copy): the closure (types and values) of `ZInQ.OneProof.frozenTarget`, checked for the types of the
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
    -- fold34-ht: HodgeTateDecompAbVar must not be a hypothesis (it stays in the closure as a proved statement);
    -- the leaf-fold32b T9 inputs of hodgetate-from-dr's proof must stay absent
    `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar, `ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists,
    `ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_open,
    `ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_printed,
    `HDec.HSyn.OpenResearchLeaves31, `HDec.HSyn.OpenResearchLeaves32,
    -- earlier folds (must stay absent)
    `PicDict.MumfordPhiSurjectiveAC, `PicFix.phiAmpleIsogeny_of_printed,
    `T09Pic.PicZeroAbVar, `PicDict.PicZeroSmooth, `T09Pic.PhiAmpleIsogeny, `HDec.WeilPairing.T09_SymmIsogenyExists,
    `PicFix.MumfordKLFiniteSectionAC,
    `CToPrinted.SGA3_VIB_3_10, `SGA3IdComp.SGA3_VIB_3_10_Nbhd, `DictModels.MumfordConn.MumfordGroupLawConn,
    `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw,
    `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite, `sorryAx,
    -- present as proved statements
    `PicZeroChar0.T09_SymmIsogenyExists0, `PicZeroChar0.PicZeroAbVar0, `T09Pic.WeilPairingMumford]
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
