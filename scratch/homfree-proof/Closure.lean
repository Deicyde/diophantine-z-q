import ZInQKernel.OneProof.Main
import Lean
/-! homfree-proof: closure constants of `frozenTarget` whose type mentions T6 / HomFreeFiniteAlgClosed /
HomRankBound (adapted from faltings-cm's Closure.lean). -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def isTgt (n : Name) : Bool :=
  match n with
  | .str _ s => s == "HomFreeFinite" || s == "HomFreeFiniteAlgClosed" || s == "HomRankBound"
  | _ => false

run_cmd do
  let env ← getEnv
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
  IO.println s!"closure size {seen.size}"
  for c in seen.toList do
    if isTgt c then
      IO.println s!"TARGET {c}"
  let mut out : Array String := #[]
  for c in seen.toList do
    if let some ci := env.find? c then
      let ty := ci.type.getUsedConstants
      let isProj := (env.getProjectionFnInfo? c).isSome
      if ty.any (fun n => isTgt n) then
        out := out.push s!"TYPE {c} proj={isProj}"
  for c in seen.toList do
    if let some (.defnInfo v) := env.find? c then
      if v.value.getUsedConstants.any isTgt && !(v.type.getUsedConstants.any isTgt) then
        out := out.push s!"DEFVAL {c}"
  for s in out.qsort (· < ·) do IO.println s
