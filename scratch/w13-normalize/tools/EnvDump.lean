/-
Offline environment-fact dump for the W13 source normalization (analysis tool, not production).
Imports the given built modules and writes, per imported module: direct imports, namespaces it
registers, its public constants (with a protected flag), instance names (global or scoped
namespace), simp-set entries (default `simp` set), and name aliases (`export`).
It reads facts only; it adds no declarations.
-/
import Lean
open Lean Meta

def jstr (s : String) : String := Lean.Json.compress (Lean.Json.str s)

unsafe def nsEntries (md : ModuleData) : Array Name := Id.run do
  let mut out := #[]
  for (extName, es) in md.entries do
    if extName.toString.endsWith "namespacesExt" then
      for e in es do
        out := out.push (unsafeCast e : Name)
  return out

unsafe def main (args : List String) : IO Unit := do
  let modsFile := args[0]!
  let outFile := args[1]!
  let mods := (← IO.FS.lines modsFile).filter (· ≠ "") |>.map (·.toName)
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024) (loadExts := false)
  let h ← IO.FS.Handle.mk outFile .write
  let names := env.header.moduleNames
  -- list extension names once (diagnostic)
  if h' : 0 < env.header.moduleData.size then
    let md := env.header.moduleData[0]
    let ens := md.entries.map (·.1.toString)
    h.putStrLn s!"\{\"extnames\":{Lean.Json.compress (Lean.toJson ens)}}"
  for i in [0:names.size] do
    let m := names[i]!
    let md := env.header.moduleData[i]!
    let imps := md.imports.map (fun im => im.module.toString)
    let ns := (nsEntries md).map toString
    let mut consts : Array Json := #[]
    for c in md.constNames do
      if isPrivateName c then continue
      let prot := isProtected env c
      consts := consts.push (Json.arr #[Json.str c.toString, Json.bool prot])
    let mut insts : Array Json := #[]
    for e in instanceExtension.ext.getModuleEntries env i do
      match e with
      | .global ie => if let some n := ie.globalName? then insts := insts.push (Json.arr #[Json.str n.toString, Json.null])
      | .scoped sn ie => if let some n := ie.globalName? then insts := insts.push (Json.arr #[Json.str n.toString, Json.str sn.toString])
    let mut simps : Array Json := #[]
    for e in simpExtension.ext.getModuleEntries env i do
      let (sn, se) := match e with
        | .global se => (Json.null, se)
        | .scoped sn se => (Json.str sn.toString, se)
      match se with
      | .thm t =>
        match t.origin with
        | .decl n _ _ => simps := simps.push (Json.arr #[Json.str n.toString, sn, Json.str "thm"])
        | _ => pure ()
      | .toUnfold n => simps := simps.push (Json.arr #[Json.str n.toString, sn, Json.str "unfold"])
      | .toUnfoldThms n _ => simps := simps.push (Json.arr #[Json.str n.toString, sn, Json.str "unfoldThms"])
    let mut als : Array Json := #[]
    for (a, t) in aliasExtension.getModuleEntries env i do
      als := als.push (Json.arr #[Json.str a.toString, Json.str t.toString])
    let j := Json.mkObj [("m", Json.str m.toString), ("imports", Lean.toJson imps), ("ns", Lean.toJson ns),
      ("consts", Json.arr consts), ("inst", Json.arr insts), ("simp", Json.arr simps), ("alias", Json.arr als)]
    h.putStrLn j.compress
  h.flush
  IO.println s!"modules {names.size}"
