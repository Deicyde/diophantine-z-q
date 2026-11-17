import ZInQKernel.OneProof.Main
import Lean
/-! fold34-pr (from fold33-pic's ClosureCheck): the closure (types and values) of `ZInQ.OneProof.frozenTarget`.
Prints `contains <name>: <bool>` for each checked name and, for every bundle binder of `frozenTarget`, each field
whose type mentions a checked Prop. After the folds, `AvSplit.MumfordTorsionAlgClosed` and
`ZInQ.HomLattice.GAGAMorphism` stay in the closure as proved statements (the providers' types), so the check is
that no bundle field has them as type, and that `sorryAx` is absent. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let names : List Name := [`AvSplit.MumfordTorsionAlgClosed, `ZInQ.HomLattice.GAGAMorphism, `sorryAx,
    `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof,
    `ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof,
    -- earlier folds (must stay absent)
    `CToPrinted.SGA3_VIB_3_10, `SGA3IdComp.SGA3_VIB_3_10_Nbhd, `DictModels.MumfordConn.MumfordGroupLawConn,
    `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite, `PicDict.MumfordPhiSurjectiveAC,
    `T09Pic.PicZeroAbVar, `PicDict.PicZeroSmooth]
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
