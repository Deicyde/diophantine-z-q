/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see Contrib/CloudW03NeronSurj/LICENSE and NOTICE.
Derived from P2M/Util.lean in anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2.

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-14, H5 lane4 Lean 4.35 port.
This file supplies the source port-utility commands that the published H76 port utility
`ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil` does not provide, for the same isolated port
prefix `ZInQ.Contrib.CloudW03NeronSurj.FLT`:
  * `r2nos_open_scoped`        = source `p2m_open_scoped` (root and prefixed namespace);
  * `#r2nos_type_eq_warn`      = source `#p2m_type_eq_warn` (prefix-aware constant lookup);
  * `r2nos_alias`              = source `p2m_alias` (silent on a missing target, as in source);
and two mechanical-port shims documented below (`r2nos_open_dual`, `r2nos_erase_attr`).
None of these commands adds a declaration, axiom or proof step; they only change name
resolution scopes, attribute erasure and diagnostics during elaboration.
-/
import Lean
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt

open Lean Elab Command

/-- The H76 port prefix shared by every vendored declaration. -/
def portPrefix : Name := ZInQ.Contrib.CloudW03NeronSurj.PortUtil.portPrefix

/-- The port splits every root-level source namespace `X` into Mathlib's root `X` and the
isolated `portPrefix ++ X`.  `otherHalf c` is the counterpart of a resolved namespace `c`. -/
def otherHalf (c : Name) : Name :=
  if portPrefix.isPrefixOf c then c.replacePrefix portPrefix .anonymous else portPrefix ++ c

/-- Shim inserted by the mechanical port immediately after a source `open`/`open scoped`/
`open … hiding` command.  For each namespace token `n` of that command, every namespace `c` that
Lean's own `open` resolution yields in the current scope (scope match and open-declaration
matches) is completed by its other half `otherHalf c`, opened (or, for `open scoped`, only
activated) with the same hidden names (`n~h₁~h₂`).  This is exactly the single root namespace the
unprefixed source opened.  Counterparts that do not exist are harmless no-ops. -/
def openDual (s : String) (scopedOnly : Bool) : CommandElabM Unit := do
  for w in s.splitOn " " do
    if w.isEmpty then continue
    let parts := w.splitOn "~"
    let n := parts.head!.toName
    let hidden := (parts.drop 1).filter (· ≠ "") |>.map (·.toName)
    let env ← getEnv
    let cur ← getCurrNamespace
    let ods ← getOpenDecls
    let cands := ResolveName.resolveNamespace env cur ods (n.replacePrefix `_root_ .anonymous)
    let cands := if n.getRoot == `_root_ then [n.replacePrefix `_root_ .anonymous] ++ cands else cands
    for c in cands do
      let k := otherHalf c
      -- a root half can only come from imports, so it must exist now; a prefixed half may be
      -- created later in this very file (as the single source namespace was), so keep it.
      if env.isNamespace k || portPrefix.isPrefixOf k then
        unless scopedOnly do
          let od := OpenDecl.simple k hidden
          unless (← getOpenDecls).contains od do
            modifyScope fun sc => { sc with openDecls := od :: sc.openDecls }
        activateScoped k

/-- Shim inserted by the mechanical port immediately after every source `namespace` command.
In the unprefixed source, inside `namespace A.B` the names of Mathlib's `A.B.*` and `A.*` resolve
through the current namespace and their scoped extensions are active.  The port's current
namespace is `portPrefix ++ A.B`, so for each scope whose namespace lies strictly below the
prefix, the root counterparts `A`, `A.B` that exist are added as open declarations of that
scope, and the innermost ones' scoped extensions are activated. -/
def namespaceDual : CommandElabM Unit := do
  let env ← getEnv
  let st ← get
  let fix (sc : Scope) : Scope := Id.run do
    let ns := sc.currNamespace
    if !(portPrefix.isPrefixOf ns) || ns == portPrefix then return sc
    let rel := ns.replacePrefix portPrefix .anonymous
    let comps := rel.components
    let mut acc : Name := .anonymous
    let mut ods := sc.openDecls
    for c in comps do
      acc := acc ++ c
      let od := OpenDecl.simple acc []
      if env.isNamespace acc && !ods.contains od then
        ods := od :: ods
    return { sc with openDecls := ods }
  set { st with scopes := st.scopes.map fix }
  let cur ← getCurrNamespace
  if portPrefix.isPrefixOf cur && cur != portPrefix then
    let rel := cur.replacePrefix portPrefix .anonymous
    let mut acc : Name := .anonymous
    for c in rel.components do
      acc := acc ++ c
      if env.isNamespace acc then activateScoped acc

end ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt

open Lean Elab Command in
elab "r2nos_open_dual " s:str : command =>
  ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt.openDual s.getString false

open Lean Elab Command in
elab "r2nos_open_scoped_dual " s:str : command =>
  ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt.openDual s.getString true

open Lean Elab Command in
elab "r2nos_namespace_dual" : command =>
  ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt.namespaceDual

syntax (name := r2nosOpenDualIn) "r2nos_open_dual " str " in" ppLine command : command
syntax (name := r2nosOpenScopedDualIn) "r2nos_open_scoped_dual " str " in" ppLine command : command
open Lean in
macro_rules
  | `(r2nos_open_dual $s:str in $c:command) =>
    return mkNullNode #[← `(section), ← `(r2nos_open_dual $s:str), c, ← `(end)]
open Lean in
macro_rules
  | `(r2nos_open_scoped_dual $s:str in $c:command) =>
    return mkNullNode #[← `(section), ← `(r2nos_open_scoped_dual $s:str), c, ← `(end)]

/- Source `p2m_open_scoped`: activate the scoped extensions of each listed namespace, for both
the root name and the prefixed name. -/
open Lean Elab Command in
elab "r2nos_open_scoped " s:str : command => do
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    let ns := ((w.splitOn "~").head!).toName
    for n in [ns, ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt.portPrefix ++ ns] do
      activateScoped n

syntax (name := r2nosOpenScopedIn) "r2nos_open_scoped " str " in" ppLine command : command
open Lean in
macro_rules
  | `(r2nos_open_scoped $s:str in $c:command) =>
    return mkNullNode #[← `(section), ← `(r2nos_open_scoped $s:str), c, ← `(end)]

/- Source `p2m_alias`, prefix-aware like H76's `w03_alias`, but (as in source) a missing target
is not an error; it is reported as a warning so the port log records it. -/
open Lean Elab Command in
elab "r2nos_alias " a:str n:str : command => do
  let env ← getEnv
  let pref := ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt.portPrefix
  let targetName := n.getString.toName
  let scopedTarget := if pref.isPrefixOf targetName then targetName else pref ++ targetName
  let candidates := [scopedTarget, targetName,
    mkPrivateName env scopedTarget, mkPrivateName env targetName]
  match candidates.find? (fun name => env.contains name) with
  | some target =>
    let aliasName := a.getString.toName
    let scopedAlias := if pref.isPrefixOf aliasName then aliasName else pref ++ aliasName
    modifyEnv fun env => addAlias env scopedAlias target
  | none => logWarning m!"r2nos_alias: target not found (source p2m_alias is a no-op here): {targetName}"

/- Shim for the source's `attribute [-instance] …` / `attribute [-simp] …` elaboration guards:
each listed name is resolved in the current scope exactly like `attribute`; a name that does not
exist at the fixed pins, or no longer carries the attribute, is reported as a warning instead of
aborting (these lines only remove instances/simp lemmas; they are not proof steps). -/
open Lean Elab Command in
elab "r2nos_erase_attr " k:str s:str : command => do
  let attrName := k.getString.toName
  let env ← getEnv
  let attr ← match getAttributeImpl env attrName with
    | .ok a => pure a
    | .error e => throwError e
  for w in s.getString.splitOn " " do
    if w.isEmpty then continue
    let id := mkIdent w.toName
    let declName? ← liftTermElabM do
      try
        let n ← realizeGlobalConstNoOverload id
        pure (some n)
      catch _ => pure none
    match declName? with
    | none => logWarning m!"r2nos_erase_attr: [-{attrName}] skipped, unknown constant {w}"
    | some declName =>
      try
        liftCoreM (attr.erase declName)
      catch e =>
        logWarning m!"r2nos_erase_attr: [-{attrName}] {declName} skipped: {e.toMessageData}"

/- Source `#p2m_type_eq_warn` with the port-prefix lookup of H76's commands. -/
open Lean Elab Command Meta in
elab "#r2nos_type_eq_warn " a:ident b:ident : command => liftTermElabM do
  let pref := ZInQ.Contrib.CloudR2NOS.Source.PortUtilExt.portPrefix
  let env ← getEnv
  let look (n : Name) : Option ConstantInfo :=
    (env.find? (pref ++ n)).orElse fun _ => env.find? n
  let some ia := look a.getId | throwError m!"#r2nos_type_eq_warn: unknown constant {a.getId}"
  let some ib := look b.getId | throwError m!"#r2nos_type_eq_warn: unknown constant {b.getId}"
  let la ← ia.levelParams.mapM fun _ => mkFreshLevelMVar
  let lb ← ib.levelParams.mapM fun _ => mkFreshLevelMVar
  let ta := ia.type.instantiateLevelParams ia.levelParams la
  let tb := ib.type.instantiateLevelParams ib.levelParams lb
  if ← isDefEq ta tb then logInfo m!"P2M_TYPE_EQ {a.getId} {b.getId}"
  else logWarning m!"P2M_DUP_TYPE_MISMATCH (non-fatal)\n  {a.getId} : {ta}\n  {b.getId} : {tb}"
