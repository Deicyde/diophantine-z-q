import ZInQKernel.OneProof.Main
/-! fold-cm: closure check of the folded frozen target (copied from fold-c8, fold-b116). The removed Props must not occur in
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
    -- removed by fold-cm (must be false): component 1 (Gonzalez-Rotger 5.12, R5ptProps, NoCM, old tops) and
    -- component 2 (the X6 rows and clauses, Elkies, Baba-Granath on X6, the X6 conic)
    `GR512Bridge.GonzalezRotgerThm512X6RCF, `GRDict.GonzalezRotgerThm512X6, `GRDict.r5ptProps_of_thm512,
    `GRX6AbPrint.gonzalezRotgerX6Ab_of_print, `LeafQM.AV.R5ptProps, `HDec.FS5NoCM.R1R2fpFullProps,
    `HDec.HSyn.sixContactMin_of_open4_hf_pz_eb_u_c8, `HDec.HSyn.sixContactMin_of_open4_hf_pz_eb,
    `HDec.HSyn.OpenResearchLeaves61, `HDec.HSyn.OpenResearchLeaves62, `HDec.HSyn.sixContactMin_of_open80,
    `HDec.HSyn.sixContactMin_of_open81,
    `LeafQM.AV.X6Props, `LeafQM.AV.R2X6Props, `LeafQM.AV.CMExists, `LeafQM.AV.X6Surj, `HDec.LeafAdopt.R2X6PropsIff,
    `X6ALIdeal.X6CoarseModuliIdeal, `X6ALIdeal.ElkiesX6StarEveryIdeal, `GRX6AbPrint.X6CoarseModuli,
    `HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery, `HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted,
    `HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField, `HDec.QMSplit.Moduli.ElkiesEquationsX6Ab,
    `HDec.QMSplit.Moduli.BabaGranathRationalAb, `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab_r5,
    `HDec.QMSplit.Moduli.GonzalezRotgerX6, `HDec.QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse,
    `GRX6AbPrint.x6ModuliWitness_of_coarse, `SGRDirect.elkies_coordinate, `HDec.X6Kummer.X6ConicModel,
    `HDec.LeafAdopt.R1R2fpRepW, `HDec.LeafAdopt.R1R2fpRepW_r5, `LeafQM.AV.R1R2fp,
    -- the new route (must be true)
    `HDec.CMBranch.CMFibreSplit, `HDec.CMBranch.FowlerProp27, `HDec.CMBranch.CMjDegree, `HDec.CMBranch.CMPotentialGood,
    `HDec.CMBranch.CMHeight62, `HDec.CMBranch.coxProperLattice_proof, `HDec.CMBranch.HeightAdditivityUpper,
    `HDec.CMBranch.ReducedCMPeriod, `Y3X6.R1R2fpY3, `Y3P1j.Y3ToP1j, `SGRDirect.HeckeSqrtBranchAny,
    `HDec.HSyn.OpenResearchLeaves63, `HDec.HSyn.sixContactMin_of_open82,
    `HDec.G0Galois.C8Conrad.ConradAppB, `DeRhamScholze.HTMerge.ScholzeH1AbVar]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"
    -- every Gonzalez-Rotger-, R5pt-, NoCM- or X6-named constant left in the closure
    let has (x y : String) : Bool := (x.splitOn y).length > 1
    let gr := s.toList.filter (fun n => let x := n.toString; has x "GonzalezRotger" || has x "gonzalezRotger")
    IO.println s!"  GonzalezRotger-named constants in the closure: {gr.length} {gr.take 60}"
    let r5 := s.toList.filter (fun n => let x := n.toString; has x "R5pt" || has x "r5pt" || has x "NoCM" || has x "FS5")
    IO.println s!"  R5pt/NoCM/FS5-named constants in the closure: {r5.length} {r5.take 60}"
    let x6 := s.toList.filter (fun n => let x := n.toString; has x "X6" || has x "x6")
    IO.println s!"  X6-named constants in the closure: {x6.length} {x6.take 80}"

/-! Field check (edit the two bundle names per fold): fold-cm component 2, `OpenResearchLeaves63` has `OpenResearchLeaves62`'s fields
without `x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal`, plus `y3ToP1j`, `heckeSqrtBranchAny`, every other field with the same type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o := `HDec.HSyn.OpenResearchLeaves62
  let n := `HDec.HSyn.OpenResearchLeaves63
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"field check: {o} {fo.size} fields, {n} {fn.size} fields; only in old: {fo.filter (!fn.contains ·)}; only in new: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"
