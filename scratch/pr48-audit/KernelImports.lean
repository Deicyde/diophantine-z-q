import Lean

open Lean

private def addRefs (out : Array Name) (expr : Expr) : Array Name := Id.run do
  let mut out := out
  for ref in expr.getUsedConstants do
    out := out.push ref
  return out

private def references (info : ConstantInfo) : Array Name := Id.run do
  let mut out := addRefs #[] info.type
  if let some value := info.value? (allowOpaque := true) then
    out := addRefs out value
  match info with
  | .inductInfo data =>
    for ctor in data.ctors do
      out := out.push ctor
  | .ctorInfo data => out := out.push data.induct
  | .recInfo data =>
    for rule in data.rules do
      out := addRefs (out.push rule.ctor) rule.rhs
  | _ => pure ()
  return out

private def moduleOf (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  env.allImportedModuleNames[idx.toNat]?

def main (args : List String) : IO Unit := do
  let [addedFile] := args | throw (IO.userError "expect a list of added module names")
  initSearchPath (← findSysroot)
  let entry := `ZInQKernel.Contrib.OneProof.DSThm966PrintedProof
  let witness := `ZInQ.Contrib.CloudB3SC5DeligneSerre.dsThm966Printed
  -- Inspect kernel definitions and theorem bodies, without running environment extensions.
  let env ← importModules #[{ module := entry }] {} (leakEnv := true) (loadExts := false)
  let lines ← IO.FS.lines (System.FilePath.mk addedFile)
  let added : Std.HashSet Name := lines.foldl
    (fun acc line => if line.isEmpty then acc else acc.insert line.toName) {}
  let some witnessInfo := env.find? witness (skipRealize := true)
    | throw (IO.userError "the witness is missing")
  unless moduleOf env witness == some entry && (witnessInfo.value? true).isSome do
    throw (IO.userError "the witness body was not loaded from its entry point")

  let mut seen : Std.HashSet Name := {}
  let mut counts : Std.HashMap Name Nat := {}
  let mut todo := #[witness]
  while let some decl := todo.back? do
    todo := todo.pop
    if seen.contains decl then continue
    seen := seen.insert decl
    let some src := moduleOf env decl | continue
    -- Existing modules cannot depend on the proof files that this PR adds.
    unless added.contains src do continue
    let some info := env.find? decl (skipRealize := true)
      | throw (IO.userError s!"missing referenced declaration {decl} in {src}")
    counts := counts.insert src (counts.getD src 0 + 1)
    todo := todo ++ references info
  for (src, count) in counts.toArray do
    IO.println s!"WITNESS\t{src}\t{count}"

  let names := env.allImportedModuleNames
  let mods := env.header.moduleData
  unless names.size == mods.size do throw (IO.userError "incomplete module data")
  let mut reported := 0
  for idx in [0:names.size] do
    let src := names[idx]!
    if added.contains src then
      reported := reported + 1
      let data := mods[idx]!
      IO.println s!"MODULE\t{src}\t{data.constants.size}"
      for imp in data.imports do
        if added.contains imp.module then
          IO.println s!"IMPORT\t{src}\t{imp.module}"
      let mut needed : Std.HashSet Name := {}
      for info in data.constants do
        for ref in references info do
          if let some dep := moduleOf env ref then
            if dep != src && added.contains dep then
              needed := needed.insert dep
      for dep in needed.toArray do
        IO.println s!"KERNEL\t{src}\t{dep}"
  IO.println s!"DONE\t{reported}\t{added.size}"
