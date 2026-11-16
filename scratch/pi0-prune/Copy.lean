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
  -- tainted inductives
  let mut ws : NameSet := ({} : NameSet).insert `HDec.LeafAdopt.R1R2fpRep
  let mut changed := true
  while changed do
    changed := false
    for n in s.toList do
      if ws.contains n then continue
      if let some (.inductInfo ii) := env.find? n then
        for c in ii.ctors do
          if let some ci := env.find? c then
            if rcMentions ws ci.type then
              ws := ws.insert n; changed := true
  -- seeds: readers of the two field projections, and tainted-type constants
  let mut D : NameSet := {}
  for n in s.toList do
    if let some ci := env.find? n then
      match n with
      | .str _ l =>
        if (l == "deligneComponentsX6PrintedAb" || l == "geomConnOfAlgClosure") && (env.getProjectionFnInfo? n).isSome then
          D := D.insert n
      | _ => pure ()
      if !ci.isCtor && (env.getProjectionFnInfo? n).isNone && !ws.contains n && rcMentions ws ci.type then
        D := D.insert n
  changed := true
  while changed do
    changed := false
    for n in s.toList do
      if D.contains n || ws.contains n then continue
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
      let ty := if rcMentions ws ci.type then "T" else "-"
      let deps := match ci.value? (allowOpaque := true) with
        | some v => (v.getUsedConstants.filter fun c => D.contains c && (env.getProjectionFnInfo? c).isNone).toList.eraseDups
        | none => []
      lines := lines.push s!"{mod}:{ln} {ty} {n}{if n.isInternal then " (internal)" else ""} <- {deps}"
  logInfo m!"COPYSET {lines.size}\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"
