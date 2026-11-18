import ZInQKernel.OneProof.Main
/-! fold-b115: closure check of the folded frozen target (copied from fold-b105). The removed Props must not occur in
the closure (types and values) of `ZInQ.OneProof.frozenTarget`, nor `sorryAx`; the hypotheses of frozenTarget are
printed by `#check`. -/

#print axioms ZInQ.OneProof.frozenTarget
#check @ZInQ.OneProof.frozenTarget

open Lean in
def fcValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

open Lean in
run_cmd do
  let env ← getEnv
  let closure : Name → NameSet := fun root => Id.run do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[root]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := fcValue? ci then todo := todo ++ v.getUsedConstants
    return seen
  let checked : List Name := [`sorryAx,
    -- fold 1 (ss-faltings): removed (must be false)
    `GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34, `SGA33Steps.SGA7_IX_Cor3_3, `GaRigidity.SGA7.SGA7_IX_Cor3_3,
    `CToPrinted.SGA7_IX_3_3, `ReductB.SemistablePersistsSHcp, `ZInQ.HeightSplit.SemistableNeronBaseChange,
    `ZInQ.HeightSplit.SemistablePersists, `HDec.HSyn.OpenResearchLeaves57, `HDec.HSyn.sixContactMin_of_open76,
    -- fold 1: the new route (must be true); IX 3.5 is d2a6b's row (still true)
    `ZInQ.SSFaltings.FaltingsSemistableHeightBC, `ZInQ.SSFaltings.SemistableReductionThmIF,
    `ZInQ.SSFaltings.semistableReductionThmIF_of_raynaud, `HDec.HSyn.OpenResearchLeaves58,
    `HDec.HSyn.sixContactMin_of_open77, `HDec.HSyn.sixContactMin_of_open76_sf,
    `GaRigidity.SGA7.SGA7_IX_3_5_ForwardGeom_Def34,
    -- earlier folds still in force: false / true / true / true / true
    `ZInQ.SemistabAssembly.BostLowerBoundAnSS, `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS, `SZRaynaud.SilverbergZarhinThm35,
    `Y3RouteA.Y3FullThreeRepZ30, `CarayolRefold.CarayolThmAFrob,
    -- fold 3 (pb-dimform + htmult-model): no field change; the dimension form is in the closure after fold 3
    `HDec.PkgI4.BergerBst.IsAdmissible, `HDec.PkgI4.BmaxOne.IsAdmissibleT, `HDec.PkgI4.FontaineSt.IsPstF]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"

/-! Field check: `OpenResearchLeaves58` has `OpenResearchLeaves57`'s fields with `sga7_IX_Cor3_3_Def34` replaced by
`faltingsSemistableHeightBC`, every other field with the same type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o := `HDec.HSyn.OpenResearchLeaves57
  let n := `HDec.HSyn.OpenResearchLeaves58
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"field check: {o} {fo.size} fields, {n} {fn.size} fields; only in old: {fo.filter (!fn.contains ·)}; only in new: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"
