import ZInQKernel.OneProof.Main
import Lean
/-! sga735-finish: reverse-dependency closure (inside the closure of `sixContactMin_of_open48`) of
`RaynaudCriterionNF` (both names): what a re-typing of r6 would have to copy. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut deps : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open48]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let mut us := ci.type.getUsedConstants
      if let some v := ccValue? ci then us := us ++ v.getUsedConstants
      deps := deps.insert c us
      todo := todo ++ us
  IO.println s!"closure size {seen.size}"
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (c, us) in deps.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  let seeds : List Name := [`HDec.PkgI2.RaynaudCriterionNF, `GapNeron.RaynaudCriterionNF]
  let mut tainted : NameSet := {}
  let mut q : Array Name := #[]
  for s in seeds do
    if seen.contains s then
      tainted := tainted.insert s; q := q.push s
  while !q.isEmpty do
    let c := q.back!
    q := q.pop
    for d in rev.getD c #[] do
      if !tainted.contains d then
        tainted := tainted.insert d
        q := q.push d
  IO.println s!"rev-closure size {tainted.size}"
  let mut out : Array String := #[]
  for c in tainted.toList do
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    let sz := match env.find? c with
      | some ci => (match ccValue? ci with | some v => v.approxDepth.toNat | none => 0)
      | none => 0
    out := out.push s!"{mod} {c} {sz}"
  for s in out.qsort (· < ·) do IO.println s
