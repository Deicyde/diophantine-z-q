import ZInQKernel.OneProof.Main
import Lean
/-! pi0-prune scope probe: live constants (closure of `ZInQ.OneProof.frozenTarget`) whose type mentions
`HDec.LeafAdopt.R1R2fpRep` or a structure (transitively) carrying it; with module and line. -/
open Lean

def scClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

def scMentions (ws : NameSet) (e : Expr) : Bool := (e.find? fun x => match x with
  | .const n _ => ws.contains n
  | _ => false).isSome

run_cmd do
  let env ← getEnv
  let s := scClosure env `ZInQ.OneProof.frozenTarget
  -- tainted inductives: fixpoint
  let mut ws : NameSet := ({} : NameSet).insert `HDec.LeafAdopt.R1R2fpRep
  let mut changed := true
  while changed do
    changed := false
    for n in s.toList do
      if ws.contains n then continue
      if let some (.inductInfo ii) := env.find? n then
        for c in ii.ctors do
          if let some ci := env.find? c then
            if scMentions ws ci.type then
              ws := ws.insert n; changed := true
  let mut lines : Array String := #[]
  for n in ws.toList do lines := lines.push s!"TAINTED {n}"
  for n in s.toList do
    if ws.contains n then continue
    if let some ci := env.find? n then
      if ci.isCtor || n.isInternal then continue
      if (env.getProjectionFnInfo? n).isSome then continue
      if scMentions ws ci.type then
        let mod := match env.getModuleIdxFor? n with
          | some i => toString env.header.moduleNames[i.toNat]!
          | none => "?"
        let rng ← findDeclarationRanges? n
        let ln := match rng with | some r => toString r.range.pos.line | none => "?"
        let vs := match ci.value? (allowOpaque := true) with | some v => v.approxDepth.toNat | none => 0
        lines := lines.push s!"{mod}:{ln} {n} depth={vs}"
  logInfo m!"{String.intercalate "\n" (lines.qsort (· < ·)).toList}"
