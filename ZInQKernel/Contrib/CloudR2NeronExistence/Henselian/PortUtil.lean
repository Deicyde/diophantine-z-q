/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
Derived from P2M/Util.lean at anthropics/fermats-last-theorem
6e837e75355538c7f80bab5b956861e86c4eacc2 and the published H76 PortUtil.
NOTICE OF MODIFICATION (2026-11-14): commands are uniquely renamed h77_*;
project namespaces resolve under this isolated port or the existing H76 ABI.
Shared names are aliases to existing constants, never duplicate definitions.
Exact-reverting refuses any unresolved metavariable. No kernel rule is changed.
-/
import Lean

open Lean Elab Tactic Meta in
elab "h77_exact_reverting " e:term : tactic => do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let fvars := lctx.foldl (init := #[]) fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId
  let (_, g') ← g.revert fvars (preserveOrder := true) (clearAuxDeclsInsteadOfRevert := true)
  g'.withContext do
    let tgt ← g'.getType
    let v ← Term.withSynthesize <| elabTermEnsuringType e tgt
    let v ← instantiateMVars v
    if v.hasExprMVar then throwError "h77_exact_reverting: unassigned metavariables remain"
    g'.assign v
  replaceMainGoal []

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil
open Lean Elab Command

def portPrefix : Name := `ZInQ.Contrib.CloudR2NeronExistence.Henselian
def sharedPrefix : Name := `ZInQ.Contrib.CloudW03NeronSurj.FLT

def openCore (s : String) : CommandElabM Unit := do
  for w in s.splitOn " " do
    if w.isEmpty then continue
    let parts := w.splitOn "~"
    let ns := parts.head!.toName
    let hidden := (parts.drop 1).filter (· ≠ "") |>.map (fun h => h.toName)
    for n in [ns, sharedPrefix ++ ns, portPrefix ++ ns] do
      modifyScope fun sc => { sc with openDecls := OpenDecl.simple n hidden :: sc.openDecls }
      activateScoped n

end ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil

open Lean Elab Command in
elab "h77_open " s:str : command =>
  ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.openCore s.getString

open Lean Elab Command in
elab "h77_ns " s:str : command =>
  modifyEnv fun env => env.registerNamespace
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix ++ s.getString.toName)

open Lean Elab Command in
elab "h77_export " n:str m:str : command => do
  let env ← getEnv
  let ns := n.getString.toName
  let cur ← getCurrNamespace
  let pref := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix
  let shared := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.sharedPrefix
  let mut al : Array (Name × Name) := #[]
  for w in m.getString.splitOn " " do
    if w.isEmpty then continue
    let candidates := [pref ++ ns ++ w.toName, shared ++ ns ++ w.toName, ns ++ w.toName]
    let candidates := candidates ++ candidates.map (mkPrivateName env)
    if let some target := candidates.find? env.contains then
      al := al.push (cur ++ w.toName, target)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env

open Lean Elab Command in
elab "h77_export_all " n:str s:str : command => do
  let env ← getEnv
  let short := s.getString.toName
  let pref := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix
  let base := pref ++ n.getString.toName ++ short
  let cur ← getCurrNamespace
  let mut al : Array (Name × Name) := #[]
  for (c, _) in env.constants.toList do
    let u := (privateToUserName? c).getD c
    if base.isPrefixOf u && u != base && !u.isInternalDetail then
      al := al.push (cur ++ short ++ u.replacePrefix base Name.anonymous, c)
  modifyEnv fun env => al.foldl (fun env p => addAlias env p.1 p.2) env

open Lean Elab Command in
elab "h77_reactivate " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    let ns := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix ++ w.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env

open Lean Elab Command in
elab "h77_alias " a:str n:str : command => do
  let env ← getEnv
  let pref := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix
  let shared := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.sharedPrefix
  let targetName := n.getString.toName
  let scopedTarget := if pref.isPrefixOf targetName then targetName else pref ++ targetName
  let candidates := [scopedTarget, shared ++ targetName, targetName]
  let candidates := candidates ++ candidates.map (mkPrivateName env)
  match candidates.find? env.contains with
  | some target =>
    let aliasName := a.getString.toName
    let scopedAlias := if pref.isPrefixOf aliasName then aliasName else pref ++ aliasName
    modifyEnv fun env => addAlias env scopedAlias target
  | none => throwError "h77_alias: target not found: {targetName}"

open Lean Elab Command in
elab "h77_open_scoped " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    let ns := ((w.splitOn "~").head!).toName
    for n in [ns,
        ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.sharedPrefix ++ ns,
        ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix ++ ns] do
      activateScoped n

open Lean Elab Command in
elab "h77_import_shared" : command => do
  let env ← getEnv
  let pref := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix
  let shared := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.sharedPrefix
  let mut al : Array (Name × Name) := #[]
  for (c, _) in env.constants.toList do
    let u := (privateToUserName? c).getD c
    if shared.isPrefixOf u && u != shared && !u.isInternalDetail then
      let a := pref ++ u.replacePrefix shared Name.anonymous
      if !env.contains a then al := al.push (a, c)
  modifyEnv fun env => al.foldl (fun env p =>
    addAlias (env.registerNamespace p.1.getPrefix) p.1 p.2) env

open Lean Elab Command Meta in
elab "#h77_type_eq " a:ident b:ident : command => liftTermElabM do
  let ia ← getConstInfo a.getId
  let ib ← getConstInfo b.getId
  if ia.levelParams.length != ib.levelParams.length then
    throwError "H77 full-type certificate: universe parameter count differs"
  let levels := ia.levelParams.map Level.param
  let ta := ia.type
  let tb := ib.type.instantiateLevelParams ib.levelParams levels
  unless ← isDefEq ta tb do
    throwError "H77 full-type certificate: mismatch\n{ta}\n{tb}"
  logInfo m!"H77_FULL_TYPE_EQ {a.getId} {b.getId}"

open Lean Elab Command Meta in
elab "#h77_type_eq_warn " a:ident b:ident : command => liftTermElabM do
  let ia ← getConstInfo a.getId
  let ib ← getConstInfo b.getId
  let la ← ia.levelParams.mapM fun _ => mkFreshLevelMVar
  let lb ← ib.levelParams.mapM fun _ => mkFreshLevelMVar
  let ta := ia.type.instantiateLevelParams ia.levelParams la
  let tb := ib.type.instantiateLevelParams ib.levelParams lb
  if ← isDefEq ta tb then logInfo m!"H77_TYPE_EQ {a.getId} {b.getId}"
  else logWarning m!"H77_DUP_TYPE_MISMATCH (non-fatal)\n{ta}\n{tb}"

syntax (name := h77OpenIn) "h77_open " str " in" ppLine command : command
open Lean in
macro_rules
  | `(h77_open $s:str in $c:command) =>
    return mkNullNode #[← `(section), ← `(h77_open $s:str), c, ← `(end)]

macro "h77_open_scoped " s:str " in " c:command : command =>
  `(section h77_open_scoped $s $c end)

/- Isolated source namespaces still see the original Mathlib namespace API. -/
open Lean Elab Command in
elab "h77_bridge_namespace" : command => do
  let cur ← getCurrNamespace
  let pref := ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.portPrefix
  unless pref.isPrefixOf cur do
    throwError "H77 namespace isolation: source attempted to leave the owned namespace: {cur}"
  let mut original := cur.replacePrefix pref Name.anonymous
  let mut ancestors : List Name := []
  while original != Name.anonymous do
    ancestors := original :: ancestors
    original := original.getPrefix
  for ns in ancestors do
    ZInQ.Contrib.CloudR2NeronExistence.Henselian.PortUtil.openCore ns.toString

