import ZInQKernel.OneProof.Main
import Lean
/-! pi0-fold probe: in the closure of `frozenTarget`, the constants whose type or value mentions
`HDec.LeafAdopt.R1R2fpRep` directly, or (value) a projection of a structure field whose type mentions it,
or a projection of the two fields to prune. Module, line range, T/V flags. -/
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
  let rep : NameSet := ({} : NameSet).insert `HDec.LeafAdopt.R1R2fpRep
  -- projections whose type mentions R1R2fpRep, and of the two fields
  let mut projs : NameSet := {}
  for n in s.toList do
    if (env.getProjectionFnInfo? n).isSome then
      if let some ci := env.find? n then
        let isPrune := match n with
          | .str _ l => l == "deligneComponentsX6PrintedAb" || l == "geomConnOfAlgClosure"
          | _ => false
        if rcMentions rep ci.type || isPrune then projs := projs.insert n
  logInfo m!"PROJS {projs.toList}"
  let mut lines : Array String := #[]
  for n in s.toList do
    if (env.getProjectionFnInfo? n).isSome then continue
    if let some ci := env.find? n then
      if ci.isCtor then continue
      if let .recInfo _ := ci then continue
      let t := rcMentions rep ci.type
      let v := match ci.value? (allowOpaque := true) with
        | some v => rcMentions rep v
        | none => false
      let p := match ci.value? (allowOpaque := true) with
        | some v => (v.getUsedConstants.filter fun c => projs.contains c).toList.eraseDups
        | none => []
      if t || v || !p.isEmpty then
        let mod := match env.getModuleIdxFor? n with
          | some i => toString env.header.moduleNames[i.toNat]!
          | none => "?"
        let rng ← findDeclarationRanges? n
        let ln := match rng with | some r => s!"{r.range.pos.line}-{r.range.endPos.line}" | none => "?"
        lines := lines.push s!"{mod}:{ln} {if t then "T" else "-"}{if v then "V" else "-"} {n} P={p}"
  logInfo m!"SCOPE {lines.size}\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"
