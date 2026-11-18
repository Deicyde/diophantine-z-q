import ZInQKernel.OneProof.H.TailZ83
import Lean
/-! ss-faltings (adapted from d2a6-reroute's TaintD.lean and TaintD2.lean): in the closure of the top theorem,
(T) constants whose value depends transitively on a seed projection (the Cor. 3.3 fields `sga7_IX_Cor3_3_Def34`,
`sga7_IX_Cor3_3`, `sga7_IX_3_3_SHpre`, `sga7_IX_3_3_SH`, `sga7_IX_3_3`, `semistablePersistsSHcp` and height-split's
SS fields `semistableReductionThm`, `semistableNeronBaseChange`, `semistablePersists`), and (S) constants whose type
mentions a carrier (a structure whose constructor type mentions a seed type) or a seed type. -/
open Lean

def topName : Name := `HDec.HSyn.sixContactMin_of_open76

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def seedNames : List String := ["sga7_IX_Cor3_3_Def34", "sga7_IX_Cor3_3", "sga7_IX_3_3_SHpre", "sga7_IX_3_3_SH",
  "sga7_IX_3_3", "semistablePersistsSHcp", "semistableReductionThm", "semistableNeronBaseChange", "semistablePersists"]

def isSeed (env : Environment) (n : Name) : Bool :=
  match n with
  | .str _ s => seedNames.contains s && (env.getProjectionFnInfo? n).isSome
  | _ => false

def isTarget (n : Name) : Bool :=
  let s := n.toString
  s.endsWith ".SGA7_IX_Cor3_3_Def34" || s.endsWith ".SGA7_IX_Cor3_3" || s.endsWith ".SGA7_IX_3_3_SHpre" ||
    s.endsWith ".SGA7_IX_3_3_SH" || s == "CToPrinted.SGA7_IX_3_3" || s.endsWith "ReductB.SemistablePersistsSHcp" ||
    s == "ZInQ.HeightSplit.SemistableReductionThm" || s == "ZInQ.HeightSplit.SemistableNeronBaseChange" ||
    s == "ZInQ.HeightSplit.SemistablePersists"

def modOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "?"

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut valUses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[topName]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then
        let us := v.getUsedConstants
        valUses := valUses.insert c us
        todo := todo ++ us
  IO.println s!"closure size {seen.size}"
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (c, us) in valUses.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  let mut tainted : NameSet := {}
  let mut q : Array Name := #[]
  for c in seen.toList do
    if isSeed env c then
      tainted := tainted.insert c
      q := q.push c
  while !q.isEmpty do
    let c := q.back!
    q := q.pop
    for d in rev.getD c #[] do
      if !tainted.contains d then
        tainted := tainted.insert d
        q := q.push d
  let mut carriers : NameSet := {}
  for c in seen.toList do
    if let some (.ctorInfo cv) := env.find? c then
      if isStructure env cv.induct && cv.type.getUsedConstants.any isTarget then
        carriers := carriers.insert cv.induct
  for c in tainted.toList do
    if isSeed env c then
      if let some info := env.getProjectionFnInfo? c then
        if let some (.ctorInfo cv) := env.find? info.ctorName then carriers := carriers.insert cv.induct
  IO.println s!"===== SSF"
  IO.println s!"carriers {carriers.toList}"
  for c in carriers.toList do
    IO.println s!"C {modOf env c} {c}"
  let mut out : Array String := #[]
  for c in tainted.toList do
    let uses := (valUses.getD c #[]).toList.filter (fun u => (u.toString.splitOn "HDec").length > 1)
    out := out.push s!"T {modOf env c} {c} USES {uses}"
  for c in seen.toList do
    if tainted.contains c then continue
    if let some ci := env.find? c then
      let ts := ci.type.getUsedConstants
      if ts.any (carriers.contains ·) || ts.any isTarget then
        let uses := (valUses.getD c #[]).toList.filter (fun u => (u.toString.splitOn "HDec").length > 1)
        out := out.push s!"S {modOf env c} {c} USES {uses}"
  IO.println s!"tainted {tainted.size}"
  for s in out.qsort (· < ·) do IO.println s
