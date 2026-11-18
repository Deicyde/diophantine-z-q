import ZInQKernel.OneProof.H.TailZ83
import Lean
/-! d2a6-reroute (adapted from piczero-char0's Taint2.lean): in the closure of `sixContactMin_of_open76` (d2a6b: rerun on TailZ83),
(T) constants whose value depends transitively on a seed projection, and (S) constants whose type mentions a
structure carrying a seed field or `PkgI2.RaynaudCriterionNF`. Two seed sets: IX 3.5 (`sga7_IX_3_5_ForwardGeom_Def34`,
`sga7_IX_3_5_ForwardGeom`, `semistableUnipotent`, `r6`) and Cor 3.3 (`sga7_IX_Cor3_3_Def34`, `sga7_IX_3_3_SHpre`,
`sga7_IX_3_3_SH`, `sga7_IX_3_3`, `semistablePersistsSHcp`). -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def seedNames35 : List String := ["sga7_IX_3_5_ForwardGeom_Def34", "sga7_IX_3_5_ForwardGeom", "semistableUnipotent", "r6"]
def seedNames33 : List String := ["sga7_IX_Cor3_3_Def34", "sga7_IX_3_3_SHpre", "sga7_IX_3_3_SH", "sga7_IX_3_3",
  "semistablePersistsSHcp"]

def isSeed (env : Environment) (names : List String) (n : Name) : Bool :=
  match n with
  | .str _ s => names.contains s && (env.getProjectionFnInfo? n).isSome
  | _ => false

def modOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "?"

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut valUses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open76]
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
  (← IO.getStdout).flush
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (c, us) in valUses.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  for (tag, names) in [("IX35", seedNames35), ("COR33", seedNames33)] do
    IO.println s!"===== {tag}"
    let mut tainted : NameSet := {}
    let mut q : Array Name := #[]
    for c in seen.toList do
      if isSeed env names c then
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
    for c in tainted.toList do
      if isSeed env names c then
        if let some info := env.getProjectionFnInfo? c then
          if let some ci := env.find? info.ctorName then
            if let .ctorInfo cv := ci then carriers := carriers.insert cv.induct
    IO.println s!"carriers {carriers.toList}"
    let mut out : Array String := #[]
    for c in tainted.toList do
      let uses := (valUses.getD c #[]).toList.filter (fun u => (u.toString.splitOn "HDec").length > 1)
      out := out.push s!"T {modOf env c} {c} USES {uses}"
    for c in seen.toList do
      if tainted.contains c then continue
      if let some ci := env.find? c then
        let ts := ci.type.getUsedConstants
        if ts.any (carriers.contains ·) || (tag == "IX35" && ts.any (fun n => n.toString.endsWith "PkgI2.RaynaudCriterionNF")) then
          let uses := (valUses.getD c #[]).toList.filter (fun u => (u.toString.splitOn "HDec").length > 1 || (u.toString.splitOn "D2A6").length > 1)
          out := out.push s!"S {modOf env c} {c} USES {uses}"
    IO.println s!"tainted {tainted.size}"
    for s in out.qsort (· < ·) do IO.println s
