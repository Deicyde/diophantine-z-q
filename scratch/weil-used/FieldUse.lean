import ZInQKernel.OneProof.Main
import Lean
/-! weil-used: which fields of `WeilDual` / `SymmIsogeny` (built from `weilPairingMumford` via
`T09Pic.t09SymmIsogenyExists_of_leaves`) are read on the route to `ZInQ.OneProof.frozenTarget`?
For every constant in the closure of `frozenTarget`, list the watched projections / recursors /
`.proj` nodes its value mentions. -/
open Lean

def wuClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  return seen

def wuStructs : List Name := [`HDec.WeilPairing.WeilDual, `HDec.WeilPairing.SymmIsogeny,
  `HDec.WeilPairing.Polarization]

def wuWatched (env : Environment) : List Name := Id.run do
  let mut out : List Name := []
  for s in wuStructs do
    out := out ++ [s ++ `rec, s ++ `casesOn, s ++ `recOn, s ++ `mk]
    if let some info := getStructureInfo? env s then
      for f in info.fieldNames do out := out ++ [s ++ f]
  return out

/-- the structures among `wuStructs` that occur as `.proj` nodes in `e` (cached traversal). -/
def wuProjs (e : Expr) : List String :=
  wuStructs.filterMap fun st =>
    (List.range 12).findSome? fun i =>
      if (e.find? fun x => match x with
        | .proj s j _ => s == st && j == i
        | _ => false).isSome then some s!"{st}.proj{i}" else none

run_cmd do
  let env ← getEnv
  let s := wuClosure env `ZInQ.OneProof.frozenTarget
  let w := wuWatched env
  logInfo m!"closure size {s.size}; watched {w}"
  logInfo m!"in closure: t09SymmIsogenyExists_of_leaves {s.contains `T09Pic.t09SymmIsogenyExists_of_leaves}, WeilPairingMumford {s.contains `T09Pic.WeilPairingMumford}"
  let mut lines : Array String := #[]
  for n in s.toList do
    if let some ci := env.find? n then
      if let some v := ci.value? (allowOpaque := true) then
        let used := v.getUsedConstants.filter (w.contains ·)
        let ps := if (v.find? fun x => x.isProj).isSome then wuProjs v else []
        if used.size > 0 || ps.length > 0 then
          lines := lines.push s!"{n}: {used.toList} {ps}"
  logInfo m!"{String.intercalate "\n" lines.toList}"
