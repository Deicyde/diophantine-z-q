import ZInQKernel.OneProof.Main
import Lean
/-! fold-b100 (from fold-kleiman2's ClosureCheck): the closure (types and values) of `ZInQ.OneProof.frozenTarget`, checked
for the types of the removed fields. Prints `contains <name>: <bool>`. After step 1 (coeff-field-tc) the types of
`heckePrimeIntegralToRational`, `gamma1IntegralBasis`, `gamma1IntegralSpan` must be absent and
`eigenformCoeffFieldFinite_proof` present; after step 2 (gr512-bridge) `GRX6AbPrint`'s Thm 5.12 field type is no field;
after step 4 (h33-g5) `ZInQ.H33D1.TYZThm33CurveSome` is no binder. `sorryAx` must be absent. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let names : List Name := [
    `CoeffRational.HeckePrimeIntegralToRational, `Gamma1Basis.Gamma1IntegralBasis, `CoeffFieldFinite.Gamma1IntegralSpan,
    `CoeffRational.eigenformCoeffFieldFinite_of_heckePrime, `eigenformCoeffFieldFinite_proof,
    `HDec.HSyn.OpenResearchLeaves45, `HDec.HSyn.OpenResearchLeaves46, `HDec.HSyn.sixContactMin_of_open64,
    `HDec.HSyn.sixContactMin_of_open65,
    -- earlier folds (must stay absent)
    `PicFix.KleimanPicZeroProper, `PicDict.MumfordPhiSurjectiveAC, `T09Pic.PicZeroAbVar, `PicDict.PicZeroSmooth,
    `CToPrinted.SGA3_VIB_3_10, `SGA3IdComp.SGA3_VIB_3_10_Nbhd, `DictModels.MumfordConn.MumfordGroupLawConn,
    `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed, `PkgI3.HomFreeFinite, `sorryAx]
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
