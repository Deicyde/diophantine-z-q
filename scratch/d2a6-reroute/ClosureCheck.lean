import ZInQKernel.Contrib.OneProof.D2A6Chain
import Lean
/-! d2a6-reroute: which of the old and new statements occur in the closure (types and values, transitively) of the
rerouted top `sixContactMin_of_open72_u` (generated chain on `D2A6.R6U`) and, as control, of `sixContactMin_of_open72`.
`sixContactMin_of_open73` (BypassFold.lean) is `open72_u` composed with a conversion that reads only the new leaves. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def closureOf (env : Environment) (top : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[top]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then
        todo := todo ++ v.getUsedConstants
  return seen

def probes : List Name := [
  `GaRigidity.SGA7.SGA7_IX_3_5_ForwardGeom_Def34, `SGA33Steps.SGA7_IX_3_5_ForwardGeom,
  `GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34,
  `HDec.PkgI2.RaynaudCriterionNF, `PkgI2.RaynaudCriterionNF, `GapNeron.RaynaudCriterionNF,
  `HDec.LeafQM.AV.QML3.goodReduction, `HDec.G15Ram.raynaudPlace_of_R6, `HDec.G15Ram.torsFix_of_descent,
  `HDec.HSyn.modelG3G6_of_leaves3, `HDec.G0ModField.KernelField.good_of_QML3,
  `SZRaynaud.RaynaudWildNF, `SZRaynaud.ElliotWildInertiaTrivial, `SZRaynaud.SilverbergZarhinThm35,
  `SGRSplit.ShimuraIntegralModelRep, `DictModels.RaynaudOr.RaynaudSemistableSHOr, `sorryAx]

run_cmd do
  let env ← getEnv
  for top in [`HDec.HSyn.sixContactMin_of_open72_u, `HDec.HSyn.sixContactMin_of_open72] do
    let cl := closureOf env top
    IO.println s!"== {top}: closure {cl.size}"
    -- names that merely end with the probe (namespaces vary between copies)
    for p in probes do
      let hit := cl.toList.filter (fun n => n == p || n.toString.endsWith ("." ++ p.toString))
      IO.println s!"  {p}: {if hit.isEmpty then "absent" else s!"PRESENT {hit.take 3}"}"
  -- every constant whose name mentions SemistableUnipotent / ForwardGeom
  let cl := closureOf env `HDec.HSyn.sixContactMin_of_open72_u
  let bad := cl.toList.filter (fun n => (n.toString.splitOn "ForwardGeom").length > 1 ||
    (n.toString.splitOn "SemistableUnipotent").length > 1 || (n.toString.splitOn "semistableUnipotent").length > 1)
  IO.println s!"open72_u closure names with ForwardGeom/SemistableUnipotent: {bad.length} {bad.take 10}"
