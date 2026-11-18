import ZInQKernel.OneProof.Main
import Lean

open Lean

def censusValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo x => some x.value
  | .thmInfo x => some x.value
  | .opaqueInfo x => some x.value
  | _ => none

def censusModule (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def census (env : Environment) (root : Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut edges : Std.HashMap Name (Array Name) := {}
  let mut todo := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if edges.contains c then continue
    let ds := match env.find? c with
      | some ci => ci.type.getUsedConstants ++ ((censusValue? ci).map Expr.getUsedConstants).getD #[]
      | none => #[]
    edges := edges.insert c ds
    todo := todo ++ ds
  return edges

def reverseEdges (edges : Std.HashMap Name (Array Name)) : Std.HashMap Name (Array Name) :=
  edges.fold (init := {}) fun rev c deps =>
    deps.foldl (fun rev d => rev.insert d ((rev.getD d #[]).push c)) rev

def readers (rev : Std.HashMap Name (Array Name)) (seeds : Array Name)
    (stop : NameSet := {}) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := seeds
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c || stop.contains c then continue
    seen := seen.insert c
    todo := todo ++ rev.getD c #[]
  return seen

def buildSeeds : Array Name := #[
  `HDec.HSyn.OpenAddedLeaves28,
  `HDec.HSyn.OpenAddedLeaves28.scholzeH1AbVar,
  `HDec.HSyn.OpenAddedLeaves28.mk,
  `HDec.HSyn.OpenAddedLeaves28.conradAppB,
  `HDec.HSyn.OpenAddedLeaves28.t10TateDuality,
  `HDec.HSyn.GR9.OpenResearchLeaves60_y3x6,
  `HDec.HSyn.GR9.OpenResearchLeaves54SFU_y3x6,
  `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar,
  `PkgI4.DeRhamComparison, `PkgI4.DeRhamComparisonHT,
  `HDec.G0Galois.G9GlueNoT23, `HDec.G0Galois.G9Glue,
  `HDec.G0Galois.GaloisPiecesC8]

def apiSeeds : Array Name := #[
  `DeRhamScholze.HTMerge.ScholzeH1AbVar, `HDec.HSyn.OpenAddedLeaves28.scholzeH1AbVar,
  `DeRhamScholze.HTMerge.hodgeNumberH1AbVar_of_scholzeH1,
  `DeRhamScholze.HTMerge.dual_deRham_of_scholzeH1,
  `DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1,
  `DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne,
  `DeRhamScholze.HTMerge.hodgeTateDecompHom_of_scholzeH1,
  `DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne,
  `DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1,
  `HDec.HSyn.OpenResearchLeaves63.deRhamVpAbVarDirect,
  `ZInQ.Contrib.G9.g9GlueNoT23_of_fieldEmb,
  `HDec.G0Galois.C8Conrad.c8Inputs_of_leaves,
  `HDec.G0Galois.C8Conrad.g12DetPZ_of_twistFinite,
  `HDec.HSyn.HodgeLF7.r10,
  `ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT]

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let main := census env `ZInQ.OneProof.frozenTarget
  let six := census env `HDec.HSyn.sixContactMin_of_open82
  let back := reverseEdges main
  IO.println s!"headline closure: {main.size}; H closure: {six.size}"
  for c in apiSeeds do
    let refs := (back.getD c #[]).toList.eraseDups.map toString
    IO.println s!"{c}\t{main.contains c}\t{refs.mergeSort (· < ·)}"
  let sixBack := reverseEdges six
  let stop := NameSet.ofList [
    `ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or,
    `DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne,
    `DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1,
    `ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT,
    `HDec.HSyn.HodgeLF7.r10,
    `HDec.HSyn.g9Glue_of_deRhamComparisonHT,
    `HDec.HSyn.g9GlueNoT23_of_deRhamComparisonHT,
    `PkgI4.deRhamComparison_of_HT]
  let tainted := readers sixBack buildSeeds stop
  for c in tainted.toList.mergeSort (fun a b => a.toString < b.toString) do
    if six.contains c then
      let deps := ((six.getD c #[]).filter tainted.contains).toList.eraseDups
      IO.println s!"COPY\t{censusModule env c}\t{c}\t{String.intercalate " " (deps.map toString)}"
