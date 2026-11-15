import ZInQKernel.OneProof.Main
import Lean
/-! faltings-cm: closure constants of `frozenTarget` whose type mentions the Faltings Props. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def isTgt (n : Name) : Bool :=
  match n with
  | .str _ s => s == "FaltingsSemisimple" || s == "FaltingsTate"
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
  let targets : List Name := [`PkgI3.FaltingsSemisimple, `PkgI3.FaltingsTate,
     `HDec.FaltingsSemisimple, `HDec.FaltingsTate, `ObjBridge.FaltingsSemisimple, `ObjBridge.FaltingsTate]
  for c in seen.toList do
    if isTgt c then
      IO.println s!"TARGET {c}"
  for t in targets do
    logInfo m!"{t}: {seen.contains t} {env.contains t}"
  let mut out : Array String := #[]
  for c in seen.toList do
    if let some ci := env.find? c then
      let ty := ci.type.getUsedConstants
      let isProj := (env.getProjectionFnInfo? c).isSome
      if ty.any (fun n => isTgt n) then
        out := out.push s!"TYPE {c} proj={isProj} kind={match ci with | .thmInfo _ => "thm" | .defnInfo _ => "def" | .ctorInfo _ => "ctor" | .inductInfo _ => "ind" | _ => "other"}"
  for c in seen.toList do
    if let some (.defnInfo v) := env.find? c then
      if v.value.getUsedConstants.any isTgt && !(v.type.getUsedConstants.any isTgt) then
        out := out.push s!"DEFVAL {c}"
  for s in out.qsort (· < ·) do IO.println s
