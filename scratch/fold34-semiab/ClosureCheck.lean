import ZInQKernel.OneProof.Main
import Lean
/-! fold34-semiab (from fold33-pic, fold33-copy): the closure (types and values) of `ZInQ.OneProof.frozenTarget`.
Prints `contains <name>: <bool>` for each name. After this fold `ZInQ.HeightSplit.BostLowerBound`,
`GaudronRemondThm14` and `ZInQ.HeightFix.SemiAbelianDescendsPerfect` stay in the closure as proved intermediate
statements, so the check for them is that no field of a bundle of `frozenTarget` (and no binder) has one of them as
its type; the names removed by earlier folds and `sorryAx` must be absent. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let removed : List Name := [`ZInQ.HeightSplit.BostLowerBound, `ZInQ.HeightSplit.GaudronRemondThm14,
    `ZInQ.HeightFix.SemiAbelianDescendsPerfect, `ZInQ.HeightDict.BostLowerBoundPrinted,
    `ZInQ.HeightDict.GaudronRemondThm14Printed]
  let names : List Name := removed ++ [
    -- this fold: proofs and new leaves (present)
    `ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley, `ZInQ.SemiAbDescend.ChevalleyPerfect,
    `ZInQ.HeightFix.BostLowerBoundPrinted, `ZInQ.HeightFix.GaudronRemondThm14Printed,
    `ZInQ.HeightFix.IsPrintedStableHeight, `HDec.HSyn.OpenResearchLeaves32, `HDec.HSyn.sixContactMin_of_open49,
    -- earlier folds (must stay absent)
    `PicDict.MumfordPhiSurjectiveAC, `T09Pic.WeilPairingMumford, `T09Pic.PicZeroAbVar, `PicDict.PicZeroSmooth,
    `CToPrinted.SGA3_VIB_3_10, `SGA3IdComp.SGA3_VIB_3_10_Nbhd, `DictModels.MumfordConn.MumfordGroupLawConn,
    `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw, `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite,
    `ZInQ.GZDecomp.GrossZagierHeegner, `sorryAx]
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
  if let some ci := env.find? `ZInQ.OneProof.frozenTarget then
    -- binders of frozenTarget
    let mut ty := ci.type
    let mut nb := 0
    while ty.isForall do
      let d := ty.bindingDomain!
      if d.getUsedConstants.any (fun n => removed.contains n) then
        IO.println s!"  BINDER with a removed type: {d}"
      nb := nb + 1
      ty := ty.bindingBody!
    IO.println s!"  binders: {nb}"
    let bs := ci.type.getUsedConstants.filter fun n =>
      (isStructure env n) && (n.toString.startsWith "HDec.HSyn.Open")
    let mut bad := 0
    for b in bs do
      let fs := getStructureFields env b
      IO.println s!"  bundle {b}: {fs.size} fields"
      for f in fs do
        if let some p := env.find? (b ++ f) then
          let t := p.type.getForallBody
          if t.getUsedConstants.any (fun n => removed.contains n) then
            bad := bad + 1
            IO.println s!"    FIELD {f} has a removed type: {t.getUsedConstants.toList.filter (removed.contains ·)}"
    IO.println s!"  fields with a removed type: {bad}"
