import ZInQKernel.OneProof.Main
import Lean
/-! pi0-prune probe: live constants whose value transitively reads one of the two fields
(`*.deligneComponentsX6PrintedAb`, `*.geomConnOfAlgClosure` projections), or whose type mentions
`R1R2fpRep` / a structure carrying it. Module, line range. -/
open Lean

def rcClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

def rcMentions (ws : NameSet) (e : Expr) : Bool := (e.find? fun x => match x with
  | .const n _ => ws.contains n
  | _ => false).isSome

run_cmd do
  let env ← getEnv
  let s := rcClosure env `ZInQ.OneProof.frozenTarget
  let mut D : NameSet := {}
  for n in s.toList do
    let l := n.getString!
    if (l == "deligneComponentsX6PrintedAb" || l == "geomConnOfAlgClosure") && (env.getProjectionFnInfo? n).isSome then
      D := D.insert n
  logInfo m!"projections: {D.toList}"
  let mut changed := true
  while changed do
    changed := false
    for n in s.toList do
      if D.contains n then continue
      if let some ci := env.find? n then
        if let some v := ci.value? (allowOpaque := true) then
          if rcMentions D v then D := D.insert n; changed := true
  let mut lines : Array String := #[]
  for n in D.toList do
    if let some ci := env.find? n then
      if (env.getProjectionFnInfo? n).isSome then continue
      let mod := match env.getModuleIdxFor? n with
        | some i => toString env.header.moduleNames[i.toNat]!
        | none => "?"
      let rng ← findDeclarationRanges? n
      let ln := match rng with | some r => s!"{r.range.pos.line}-{r.range.endPos.line}" | none => "?"
      lines := lines.push s!"{mod}:{ln} {n}{if n.isInternal then " (internal)" else ""}"
  logInfo m!"READERS {lines.size}\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"
