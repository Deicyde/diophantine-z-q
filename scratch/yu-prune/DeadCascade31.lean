import ZInQKernel.OneProof.H.TailZ31
import Lean

/-!
# Dead cascade of the prune

Run after `PruneScan.lean` has written `scratch/yu-prune/prune-set-applied.txt`:

    lake env lean scratch/yu-prune/DeadCascade.lean

Lists the OneProof constants outside the closure of `HDec.HSyn.sixContactMin_of_open25` that read a field of
the prune set (through its projection function or a raw projection), and every constant that uses
one of those, transitively. Removing the prune set's fields deletes all of them; constants inside
the closure only lose the assignments of removed fields. Writes `scratch/yu-prune/dead-cascade.txt`.
-/

open Lean

namespace DeadCascade

def isOneProofModule (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => (`ZInQKernel.OneProof).isPrefixOf env.header.modules[idx.toNat]!.module
  | none => false

def constValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def usedConsts (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ ((constValue? ci).map (·.getUsedConstants)).getD #[]

def closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then todo := todo ++ usedConsts ci
  return seen

end DeadCascade

open DeadCascade in
run_cmd do
  let env ← getEnv
  let txt ← IO.FS.readFile "scratch/yu-prune/prune-set-applied.txt"
  -- dead fields: (structure, field name), and their projection functions
  let mut dead : Std.HashSet (Name × Name) := {}
  let mut deadProj : NameSet := {}
  for l in txt.splitOn "\n" do
    let ws := l.splitOn " "
    if ws.length == 3 && ws[0]! == "FIELD" then
      let q := ws[2]!.toName
      dead := dead.insert (q.getPrefix, Name.mkSimple q.getString!)
      deadProj := deadProj.insert q
  let cl := closure env `HDec.HSyn.sixContactMin_of_open25
  let readsDead (ci : ConstantInfo) : Bool :=
    (usedConsts ci).any deadProj.contains ||
    ([ci.type] ++ (constValue? ci).toList).any fun e => (e.find? fun
      | .proj s i _ => (getStructureFields env s)[i]?.any (fun f => dead.contains (s, f))
      | _ => false).isSome
  let mut ops : Array Name := #[]
  for (c, ci) in env.constants.toList do
    if isOneProofModule env c && !c.isInternal then ops := ops.push c
  let mut bad : NameSet := {}
  for c in ops do
    if cl.contains c || deadProj.contains c then continue
    if let some ci := env.find? c then
      if readsDead ci then bad := bad.insert c
  -- users of dead constants are dead (none of them is in the closure)
  let mut changed := true
  while changed do
    changed := false
    for c in ops do
      if bad.contains c || deadProj.contains c then continue
      if let some ci := env.find? c then
        if (usedConsts ci).any bad.contains then
          bad := bad.insert c
          changed := true
  let mut out : Array String := #[]
  for c in bad.toList do
    let mi := (env.getModuleIdxFor? c).map (fun i => toString env.header.modules[i.toNat]!.module)
    out := out.push s!"{mi.getD "?"} {c}{if cl.contains c then " (IN CLOSURE!)" else ""}"
  IO.FS.writeFile "scratch/yu-prune/dead-cascade.txt" ("\n".intercalate (out.qsort (· < ·)).toList ++ "\n")
  logInfo m!"CASCADE dead fields={dead.size} oneproof constants={ops.size} cascade={bad.size}"
