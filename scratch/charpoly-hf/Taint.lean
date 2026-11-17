import ZInQKernel.OneProof.Main
import Lean
/-! charpoly-hf (copied from homfree-noemb, seeds t7 and charPolyIndepOfEllAlgClosed): constants in `frozenTarget`'s closure whose value depends (transitively) on a
proof of T6 / HomFreeFiniteAlgClosed taken from a bundle field (`*.t6`, `*.homFreeFiniteAlgClosed`
projections), and constants whose type mentions a structure carrying such a field. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def isSeed (env : Environment) (n : Name) : Bool :=
  match n with
  | .str _ s => (s == "t7" || s == "charPolyIndepOfEllAlgClosed") && (env.getProjectionFnInfo? n).isSome
  | _ => false

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut valUses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
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
  -- reverse edges
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
  -- structures carrying the field
  let mut carriers : NameSet := {}
  for c in tainted.toList do
    if isSeed env c then
      if let some info := env.getProjectionFnInfo? c then
        if let some ci := env.find? info.ctorName then
          if let .ctorInfo cv := ci then carriers := carriers.insert cv.induct
  IO.println s!"carriers {carriers.toList}"
  let mut out : Array String := #[]
  for c in tainted.toList do
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    let uses := ((valUses.getD c #[]).filter (tainted.contains ·)).toList
    out := out.push s!"T {mod} {c} USES {uses}"
  for c in seen.toList do
    if tainted.contains c then continue
    if let some ci := env.find? c then
      if ci.type.getUsedConstants.any (carriers.contains ·) then
        let mod := match env.getModuleIdxFor? c with
          | some i => toString (env.header.moduleNames[i.toNat]!)
          | none => "?"
        out := out.push s!"S {mod} {c}"
  IO.println s!"tainted {tainted.size}"
  for s in out.qsort (· < ·) do IO.println s
