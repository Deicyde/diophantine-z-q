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

-- Only the carrier modules can contribute to the copy plan.
-- The separate dry-run checks the absence/presence in the full dependency closure.
def onCopyRoute (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "ZInQKernel.OneProof.H.Y3" ||
  s.startsWith "ZInQKernel.Contrib.OneProof.C8" ||
  s.startsWith "ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosedReroute" ||
  s.endsWith ".ScholzeH1AbVar" ||
  [ "ZInQKernel.OneProof.Main", "ZInQKernel.OneProof.H.TailZ89",
    "ZInQKernel.OneProof.H.TailZ87", "ZInQKernel.OneProof.H.C8Chain",
    "ZInQKernel.OneProof.H.PicZeroCharZeroCopy", "ZInQKernel.OneProof.H.TailA",
    "ZInQKernel.OneProof.H.TailC", "ZInQKernel.OneProof.H.TailE",
    "ZInQKernel.OneProof.H.TailS", "ZInQKernel.OneProof.H.TailV",
    "ZInQKernel.OneProof.H.LPrefix" ].contains s

def census (env : Environment) (root : Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut edges : Std.HashMap Name (Array Name) := {}
  let mut todo := [root]
  while let c :: next := todo do
    todo := next
    if edges.contains c then continue
    if !onCopyRoute (censusModule env c) then continue
    let ds := match env.find? c with
      | some ci => ci.type.getUsedConstants ++ ((censusValue? ci).map Expr.getUsedConstants).getD #[]
      | none => #[]
    edges := edges.insert c ds
    todo := ds.foldl (fun ns d => d :: ns) todo
  return edges

def descend (edges : Std.HashMap Name (Array Name)) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [root]
  while let c :: next := todo do
    todo := next
    if seen.contains c then continue
    if let some deps := edges[c]? then
      seen := seen.insert c
      todo := deps.foldl (fun ns d => d :: ns) todo
  return seen

def reverseEdges (edges : Std.HashMap Name (Array Name)) : Std.HashMap Name (List Name) :=
  edges.fold (init := {}) fun rev c deps =>
    deps.foldl (fun rev d => rev.insert d (c :: rev.getD d [])) rev

def readers (rev : Std.HashMap Name (List Name)) (seeds : Array Name)
    (stop : NameSet := {}) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := seeds.toList
  while let c :: next := todo do
    todo := next
    if seen.contains c || stop.contains c then continue
    seen := seen.insert c
    todo := (rev.getD c []).foldl (fun ns d => d :: ns) todo
  return seen

def buildSeeds : Array Name := #[
  `HDec.HSyn.OpenAddedLeaves28,
  `HDec.HSyn.OpenAddedLeaves28.scholzeH1AbVar,
  `HDec.HSyn.OpenAddedLeaves28.mk,
  `HDec.HSyn.OpenAddedLeaves28.conradAppB,
  `HDec.HSyn.OpenAddedLeaves28.t10TateDuality,
  `HDec.HSyn.OpenResearchLeaves60_y3x6,
  `HDec.HSyn.OpenResearchLeaves59_y3x6,
  `HDec.HSyn.OpenResearchLeaves54SFU_y3x6,
  `HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6,
  `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar,
  `HDec.PkgI4.DeRhamComparison, `HDec.PkgI4.DeRhamComparisonHT,
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
  `HDec.ZInQ.Contrib.G9.g9GlueNoT23_of_fieldEmb,
  `HDec.G0Galois.C8Conrad.c8Inputs_of_leaves,
  `HDec.G0Galois.C8Conrad.g12DetPZ_of_twistFinite,
  `HDec.HSyn.HodgeLF7.r10,
  `ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT]

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let main := census env `ZInQ.OneProof.frozenTarget
  let six := descend main `HDec.HSyn.sixContactMin_of_open82
  let back := reverseEdges main
  IO.println s!"carrier-module constants in headline closure: {main.size}; in H closure: {six.size}"
  for c in apiSeeds do
    let refs := (back.getD c []).eraseDups.map toString
    IO.println s!"{c}\t{main.contains c}\t{refs.mergeSort (· < ·)}"
  let stop := NameSet.ofList [
    `ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or,
    `DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne,
    `DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1,
    `ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT,
    `HDec.HSyn.HodgeLF7.r10,
    `HDec.HSyn.g9Glue_of_deRhamComparisonHT,
    `HDec.HSyn.g9GlueNoT23_of_deRhamComparisonHT,
    `PkgI4.deRhamComparison_of_HT, `HDec.PkgI4.deRhamComparison_of_HT]
  let mut tainted := readers back buildSeeds stop
  -- Constructors carry the field types of Prop bundles. Once any constructor
  -- changes, include every reader of its structure type, even if the reader
  -- only projects a different field.
  repeat
    let owners := tainted.toList.filterMap fun c =>
      match env.find? c with
      | some (.ctorInfo ci) => some ci.induct
      | _ => none
    let next := readers back (buildSeeds ++ owners.toArray) stop
    if next.size == tainted.size then break
    tainted := next
  for c in tainted.toList.mergeSort (fun a b => a.toString < b.toString) do
    if six.contains c then
      let deps := ((main.getD c #[]).filter tainted.contains).toList.eraseDups
      IO.println s!"COPY\t{censusModule env c}\t{c}\t{String.intercalate " " (deps.map toString)}"
