import ZInQKernel.OneProof.Main
import Lean

/-! rigid-prune scan: in `frozenTarget`'s closure, the definitions whose value mentions `LeafQM.AV.R1fpProps`
(transitively: the moduli-row Props), the constants whose type mentions one of them, and the constants whose value
mentions the universal clause `LeafQM.AV.R1univProps` (its genuine users). Output in scratch/rigid-prune/. -/

open Lean

namespace RigidScan

def constValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def closure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    out := out.push c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := constValue? ci then todo := todo ++ v.getUsedConstants
  return out

def modOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some idx => toString env.header.modules[idx.toNat]!.module
  | none => "?"

def mentions (e : Expr) (D : NameSet) : Bool := e.getUsedConstants.any D.contains

end RigidScan

open RigidScan in
run_cmd do
  let env ← getEnv
  let cl := closure env `ZInQ.OneProof.frozenTarget
  -- definitions transitively built on `R1fpProps`
  let mut D : NameSet := ({} : NameSet).insert `LeafQM.AV.R1fpProps
  let mut changed := true
  while changed do
    changed := false
    for c in cl do
      if D.contains c then continue
      if let some (.defnInfo v) := env.find? c then
        if mentions v.value D || mentions v.type D then
          D := D.insert c
          changed := true
  let mut outD : Array String := #[]
  for c in cl do
    if D.contains c then outD := outD.push s!"{c} {modOf env c}"
  IO.FS.writeFile "scratch/rigid-prune/scan_defs.txt" (String.intercalate "\n" (outD.qsort (· < ·)).toList ++ "\n")
  -- constants (not in D) whose type mentions D
  let mut outT : Array String := #[]
  for c in cl do
    if D.contains c then continue
    if let some ci := env.find? c then
      if mentions ci.type D then outT := outT.push s!"{c} {modOf env c}"
  IO.FS.writeFile "scratch/rigid-prune/scan_typed.txt" (String.intercalate "\n" (outT.qsort (· < ·)).toList ++ "\n")
  -- genuine users of the universal clause / of QMFamily in values
  let U : NameSet := (({} : NameSet).insert `LeafQM.AV.R1univProps).insert `LeafQM.AV.Pin.R1fpProps.univ
  let mut outU : Array String := #[]
  for c in cl do
    if let some ci := env.find? c then
      if let some v := constValue? ci then
        if mentions v U then outU := outU.push s!"{c} {modOf env c}"
  IO.FS.writeFile "scratch/rigid-prune/scan_univ_users.txt" (String.intercalate "\n" (outU.qsort (· < ·)).toList ++ "\n")
  let F : NameSet := ({} : NameSet).insert `LeafQM.AV.R1famProps
  let mut outF : Array String := #[]
  for c in cl do
    if let some ci := env.find? c then
      if let some v := constValue? ci then
        if mentions v F then outF := outF.push s!"{c} {modOf env c}"
  IO.FS.writeFile "scratch/rigid-prune/scan_fam_users.txt" (String.intercalate "\n" (outF.qsort (· < ·)).toList ++ "\n")
  logInfo m!"closure {cl.size}; defs on R1fpProps {outD.size}; typed {outT.size}; univ users {outU.size}; fam users {outF.size}"
