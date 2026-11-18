
/-! ss-faltings closure check (appended to BypassFold.lean by gen/make_check.sh): which old and new statements occur in
the closure (types and values, transitively) of the new top and, as control, of the old top. -/
open Lean in
def ssfCcValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

open Lean in
def ssfClosureOf (env : Environment) (top : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[top]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ssfCcValue? ci then
        todo := todo ++ v.getUsedConstants
  return seen

open Lean in
run_cmd do
  let env ← getEnv
  let probes : List Name := [`GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34, `SGA33Steps.SGA7_IX_Cor3_3,
    `GaRigidity.SGA7.SGA7_IX_Cor3_3, `CToPrinted.SGA7_IX_3_3, `ReductB.SemistablePersistsSHcp,
    `ZInQ.HeightSplit.SemistableNeronBaseChange, `ZInQ.HeightSplit.SemistablePersists,
    `ZInQ.HeightSplit.SemistableReductionThm, `GaRigidity.SGA7.SGA7_IX_3_5_ForwardGeom_Def34,
    `ZInQ.SSFaltings.FaltingsSemistableHeightBC, `ZInQ.SSFaltings.SemistableReductionThmIF,
    `SZRaynaud.SilverbergZarhinThm35, `sorryAx]
  for top in [`HDec.HSyn.@NEWTOP@, `HDec.HSyn.@OLDTOP@] do
    let cl := ssfClosureOf env top
    IO.println s!"== {top}: closure {cl.size}"
    for p in probes do
      let hit := cl.toList.filter (fun n => n == p || n.toString.endsWith ("." ++ p.toString))
      IO.println s!"  {p}: {if hit.isEmpty then "absent" else s!"PRESENT {hit.take 3}"}"
