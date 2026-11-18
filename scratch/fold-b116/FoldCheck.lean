import ZInQKernel.OneProof.Main
/-! fold-b116: closure check of the folded frozen target (copied from fold-b105). The removed Props must not occur in
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
    -- removed by item 2 (d2a6b) and by ss-faltings (must be false)
    `GaRigidity.SGA7.SGA7_IX_3_5_ForwardGeom_Def34, `SGA33Steps.SGA7_IX_3_5_ForwardGeom,
    `HDec.PkgI2.RaynaudCriterionNF, `PkgI2.RaynaudCriterionNF, `GapNeron.RaynaudCriterionNF,
    `HDec.G15Ram.raynaudPlace_of_R6, `HDec.G15Ram.torsFix_of_descent, `HDec.HSyn.modelG3G6_of_leaves3,
    `HDec.G0ModField.KernelField.good_of_QML3, `SGRSplit.ShimuraIntegralModelRep,
    `GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34, `SGA33Steps.SGA7_IX_Cor3_3, `GaRigidity.SGA7.SGA7_IX_Cor3_3,
    `CToPrinted.SGA7_IX_3_3, `ZInQ.HeightSplit.SemistableNeronBaseChange, `ZInQ.HeightSplit.SemistablePersists,
    `HDec.HSyn.OpenResearchLeaves58, `HDec.HSyn.sixContactMin_of_open77, `HDec.HSyn.OpenResearchLeaves59, `HDec.HSyn.sixContactMin_of_open78, `HDec.HSyn.OpenResearchLeaves60, `HDec.HSyn.sixContactMin_of_open79,
    -- the new route (must be true)
    `SZRaynaud.RaynaudWildNF, `SZRaynaud.ElliotWildInertiaTrivial, `SZRaynaud.SilverbergZarhinThm35,
    `Y3RouteA.Y3FullThreeRepZ30, `ZInQ.SSFaltings.FaltingsSemistableHeightBC, `HDec.D2A6.R6U,
    `HDec.HSyn.sixContactMin_of_open73_sf_u, `HDec.HSyn.OpenResearchLeaves59, `HDec.HSyn.sixContactMin_of_open78,
    -- earlier folds still in force: false / true / true
    `ZInQ.SemistabAssembly.BostLowerBoundAnSS, `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS, `CarayolRefold.CarayolThmAFrob,
    -- item 3 (r16-thm1b): afShimura/heckeJ1DS fields, the new leaves, G1 Prop kept out
    `AfTateLam.AfShimura, `AfTateLam.HeckeJ1DS, `R16Thm1b.ShimuraThm1Af, `R16Thm1.BShStandardModel,
    `R16Thm1.ShimuraTotalToComponents, `R16ShimuraLi.ShimuraTotalToComponents]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"
    -- every SGA 7 statement left in the closure (names containing SGA7 or sga7)
    let sga := s.toList.filter (fun n => let x := n.toString; (x.splitOn "SGA7").length > 1 || (x.splitOn "sga7").length > 1)
    IO.println s!"  SGA7-named constants in the closure: {sga.length} {sga.take 40}"

/-! Field check (edit the two bundle names per fold): item 2, `OpenResearchLeaves59` has `OpenResearchLeaves58`'s fields with
`sga7_IX_3_5_ForwardGeom_Def34` replaced by `elliotWildInertiaTrivial`, every other field with the same type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o := `HDec.HSyn.OpenResearchLeaves59
  let n := `HDec.HSyn.OpenResearchLeaves60
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"field check: {o} {fo.size} fields, {n} {fn.size} fields; only in old: {fo.filter (!fn.contains ·)}; only in new: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"
