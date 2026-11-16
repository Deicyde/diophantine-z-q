/-
Derived from P2M/Util.lean in anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache-2.0).
Changes: renamed commands for this isolated port; resolve project names beneath
ZInQ.Contrib.CloudW03NeronSurj.FLT, retaining Mathlib's original namespaces.
See NOTICE.md in this directory for provenance and license notices.
-/
import Lean

open Lean Elab Tactic Meta in
elab "w03_exact_reverting " e:term : tactic => do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let fvars := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  let (_, g') ← g.revert fvars (preserveOrder := true) (clearAuxDeclsInsteadOfRevert := true)
  g'.withContext do
    let tgt ← g'.getType
    let v ← Term.withSynthesize <| elabTermEnsuringType e tgt
    let v ← instantiateMVars v
    if v.hasExprMVar then throwError "w03_exact_reverting: unassigned metavariables remain"
    g'.assign v
  replaceMainGoal []

namespace ZInQ.Contrib.CloudW03NeronSurj.PortUtil

open Lean Elab Command

def portPrefix : Name := `ZInQ.Contrib.CloudW03NeronSurj.FLT

def openCore (s : String) : CommandElabM Unit := do
  for w in s.splitOn " " do
    if w.isEmpty then continue
    let parts := w.splitOn "~"
    let ns := parts.head!.toName
    let hidden := (parts.drop 1).filter (· ≠ "") |>.map (fun h => h.toName)
    for n in [ns, portPrefix ++ ns] do
      modifyScope fun sc => { sc with openDecls := OpenDecl.simple n hidden :: sc.openDecls }
      activateScoped n

end ZInQ.Contrib.CloudW03NeronSurj.PortUtil

open Lean Elab Command in
elab "w03_open " s:str : command =>
  ZInQ.Contrib.CloudW03NeronSurj.PortUtil.openCore s.getString

open Lean Elab Command in
elab "w03_ns " s:str : command =>
  modifyEnv fun env => env.registerNamespace
    (ZInQ.Contrib.CloudW03NeronSurj.PortUtil.portPrefix ++ s.getString.toName)

open Lean Elab Command in
elab "w03_export " n:str m:str : command => do
  let env ← getEnv
  let ns := n.getString.toName
  let cur ← getCurrNamespace
  let pref := ZInQ.Contrib.CloudW03NeronSurj.PortUtil.portPrefix
  let mut al : Array (Name × Name) := #[]
  for w in m.getString.splitOn " " do
    if w.isEmpty then continue
    let full := pref ++ ns ++ w.toName
    let global := ns ++ w.toName
    if env.contains full then al := al.push (cur ++ w.toName, full)
    else if env.contains global then al := al.push (cur ++ w.toName, global)
    else
      let prv := mkPrivateName env full
      if env.contains prv then al := al.push (cur ++ w.toName, prv)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env

open Lean Elab Command in
elab "w03_export_all " n:str s:str : command => do
  let env ← getEnv
  let short := s.getString.toName
  let base := ZInQ.Contrib.CloudW03NeronSurj.PortUtil.portPrefix ++ n.getString.toName ++ short
  let cur ← getCurrNamespace
  let mut al : Array (Name × Name) := #[]
  for (c, _) in env.constants.map₂.toList do
    let u := (privateToUserName? c).getD c
    if base.isPrefixOf u && u != base && !u.isInternalDetail then
      al := al.push (cur ++ short ++ u.replacePrefix base Name.anonymous, c)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env

open Lean Elab Command in
elab "w03_reactivate " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    let ns := ZInQ.Contrib.CloudW03NeronSurj.PortUtil.portPrefix ++ w.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env

open Lean Elab Command in
elab "w03_alias " a:str n:str : command => do
  let env ← getEnv
  let pref := ZInQ.Contrib.CloudW03NeronSurj.PortUtil.portPrefix
  let targetName := n.getString.toName
  let scopedTarget := if pref.isPrefixOf targetName then targetName else pref ++ targetName
  let candidates := [scopedTarget, targetName,
    mkPrivateName env scopedTarget, mkPrivateName env targetName]
  match candidates.find? (fun name => env.contains name) with
  | some target =>
    let aliasName := a.getString.toName
    let scopedAlias := if pref.isPrefixOf aliasName then aliasName else pref ++ aliasName
    modifyEnv fun env => addAlias env scopedAlias target
  | none => throwError "w03_alias: target not found: {targetName}"

syntax (name := w03OpenIn) "w03_open " str " in" ppLine command : command
open Lean in
macro_rules
  | `(w03_open $s:str in $c:command) =>
    return mkNullNode #[← `(section), ← `(w03_open $s:str), c, ← `(end)]
