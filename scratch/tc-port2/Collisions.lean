import Lean
/-!
Static name-collision check (tc-port2, step 3).

Reads the `.olean` files listed in the file given as first argument (lines `group<TAB>module<TAB>path`)
without importing them, takes for each module its full constant set (the `.olean.private` part for
`module` files, which holds every kernel constant of the module, else the `.olean`), and reports
every constant name declared by two different modules. Each duplicate is classified with Lean's
own import rule (`Lean.Environment` `finalizeImport` / `subsumesInfo`, Lean v4.35.0): two
declarations of one name are merged silently iff they have the same type and universe parameters
and both are theorems with the same `all` list (or a theorem and its axiom form); otherwise
importing both modules fails with "import failed, environment already contains ...".

Run: lake env lean --run scratch/tc-port2/Collisions.lean LISTFILE
-/
open Lean

/-- Lean's `subsumesInfo` minus the axiom/axiom case (not needed: we read full private data). -/
def subsumes (c₁ c₂ : ConstantInfo) : Bool :=
  c₁.name == c₂.name && c₁.type == c₂.type && c₁.levelParams == c₂.levelParams &&
    match c₁, c₂ with
    | .thmInfo t₁, .thmInfo t₂ => t₁.all == t₂.all
    | .thmInfo t₁, .axiomInfo a₂ => t₁.all == [a₂.name] && !a₂.isUnsafe
    | _, _ => false

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

unsafe def main (args : List String) : IO UInt32 := do
  let some listFile := args.head? | throw <| IO.userError "usage: LISTFILE"
  let lines := (← IO.FS.lines listFile).filter (· ≠ "")
  -- name ↦ (group, module, cinfo) of first declaration seen
  let mut seen : Std.HashMap Name (String × String × ConstantInfo) := {}
  let mut total := 0
  let mut dups : Array String := #[]
  let mut nFatal := 0
  let mut nTol := 0
  let mut nMods := 0
  for line in lines do
    let fs := line.splitOn "\t"
    let (grp, mod, path) := (fs[0]!, fs[1]!, fs[2]!)
    let mFile : System.FilePath := path
    let pFile := OLeanLevel.private.adjustFileName mFile
    let data ← if (← pFile.pathExists) then do
        let parts ← readModuleDataParts #[mFile, OLeanLevel.server.adjustFileName mFile, pFile]
        pure parts[2]!.1
      else pure (← readModuleData mFile).1
    nMods := nMods + 1
    for c in data.constants do
      total := total + 1
      match seen[c.name]? with
      | none => seen := seen.insert c.name (grp, mod, c)
      | some (g₀, m₀, c₀) =>
        if m₀ != mod then
          let ok := subsumes c c₀ || subsumes c₀ c
          if ok then nTol := nTol + 1 else nFatal := nFatal + 1
          dups := dups.push s!"{if ok then "TOLERATED" else "FATAL"}\t{c.name}\t{g₀}:{m₀}:{kindOf c₀}\t{grp}:{mod}:{kindOf c}"
  IO.println s!"modules read: {nMods}; constants: {total}; distinct names: {seen.size}"
  IO.println s!"duplicate names across modules: {dups.size} (fatal {nFatal}, tolerated {nTol})"
  for d in dups do IO.println d
  return 0
