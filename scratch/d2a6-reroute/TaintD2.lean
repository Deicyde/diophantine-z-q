import ZInQKernel.OneProof.H.TailZ79
import Lean
/-! d2a6-reroute: carriers by constructor type. In the closure of `sixContactMin_of_open72`, every structure whose
constructor type mentions `PkgI2.RaynaudCriterionNF` or the types of the IX 3.5 seed fields (`SemistableUnipotent`,
`SGA7_IX_3_5_ForwardGeom`, `SGA7_IX_3_5_ForwardGeom_Def34`), and every constant whose type mentions one of these
carriers or `PkgI2.RaynaudCriterionNF` (with its `HDec` value uses). -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def modOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "?"

def isTarget (n : Name) : Bool :=
  let s := n.toString
  s.endsWith "PkgI2.RaynaudCriterionNF" || s.endsWith ".SemistableUnipotent" ||
    s.endsWith ".SGA7_IX_3_5_ForwardGeom" || s.endsWith ".SGA7_IX_3_5_ForwardGeom_Def34"

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut valUses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open72]
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
  let mut carriers : NameSet := {}
  for c in seen.toList do
    if let some (.ctorInfo cv) := env.find? c then
      if isStructure env cv.induct && cv.type.getUsedConstants.any isTarget then
        carriers := carriers.insert cv.induct
  IO.println s!"carriers {carriers.size} {carriers.toList}"
  let mut out : Array String := #[]
  for c in seen.toList do
    if let some ci := env.find? c then
      let ts := ci.type.getUsedConstants
      if ts.any (carriers.contains ·) || ts.any isTarget then
        let uses := (valUses.getD c #[]).toList.filter (fun u => (u.toString.splitOn "HDec").length > 1)
        out := out.push s!"S {modOf env c} {c} USES {uses}"
  for s in out.qsort (· < ·) do IO.println s
