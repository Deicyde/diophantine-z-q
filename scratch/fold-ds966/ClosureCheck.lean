import ZInQKernel.OneProof.Main
import Lean
/-! fold-ds966 (from fold33-pic's ClosureCheck): the closure (types and values) of `ZInQ.OneProof.frozenTarget`.
Prints `contains <name>: <bool>` and, for each bundle binder of frozenTarget, the fields whose type uses a checked
name. Expected: `sorryAx` absent; fold 1: `DSThm966EV.DSThm966Printed` may stay in the closure as a proved
statement (the type of `CloudB3SC5DeligneSerre.dsThm966Printed`), but no bundle field has it as type; fold 2:
`PanDict.PanPrintedP` and `PanDict.BergerPrintedVT` absent from the closure, `PanPrintedF` and `BergerSurveyF`
present as field types. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let names : List Name := [`sorryAx, `DSThm966EV.DSThm966Printed,
    `ZInQ.Contrib.CloudB3SC5DeligneSerre.dsThm966Printed,
    `HDec.PkgI4.PanDict.PanPrintedP, `HDec.PkgI4.PanDict.BergerPrintedVT, `HDec.PkgI4.PanDict.BergerPrintedV,
    `HDec.PkgI4.PanDict.PanPrintedF, `HDec.PkgI4.PanDict.BergerSurveyF, `HDec.PkgI4.PanDict.panBerger_of_F,
    `HDec.PkgI4.PanDict.panBerger_of_printedPV]
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
