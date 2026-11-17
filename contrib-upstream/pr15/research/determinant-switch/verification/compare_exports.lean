import Lake.Check.Compare
import Lake.Check.Axioms
import Lean.Data.Json.FromToJson.Basic

/-!
Local structural probe, not the protected `lake comparator` command and not
kernel replay. Uses the pinned 4.35 comparison and axiom routines directly.
Arguments: comparator.json challenge.ndjson solution.ndjson.
The primitive list is from pinned Lake/CLI/Check.lean, lines 474–507.
-/

open Lean Lake.Check

def primitives : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
  ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce,
  ``Nat, ``String, ``String.mk, ``Char, ``optParam, ``autoParam,
  ``semiOutParam, ``outParam]

def expectRejected (label : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"Negative control accepted: {label}"
  | .error err => IO.println s!"REJECTED {label}: {err}"

def main (args : List String) : IO Unit := do
  let [configPath, challengePath, solutionPath] := args
    | throw <| IO.userError "Expected config, challenge export, solution export"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile configPath)
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let allowed ← IO.ofExcept <| config.getObjValAs? (Array String) "permitted_axioms"
  let definitions ← IO.ofExcept <| config.getObjValAs? (Array String) "definition_names"
  unless names.size == 6 && definitions.isEmpty do
    throw <| IO.userError "Expected six theorems and no definition holes"
  let targets := names.map String.toName
  let legal := allowed.map String.toName
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  IO.ofExcept <| compareAt challenge solution (targets ++ legal) #[] primitives
  IO.ofExcept <| checkAxioms solution targets #[] legal
  IO.println "STRUCTURE_AND_AXIOMS_PASS declarations=6; no kernel replay or isolation"

  -- Exercise real failure paths using only in-memory copies of the export.
  let first := targets[0]!
  expectRejected "missing theorem" <|
    compareAt challenge {solution with constMap := solution.constMap.erase first}
      (targets ++ legal) #[] primitives
  let some (.thmInfo thm) := solution.constMap[first]?
    | throw <| IO.userError "Target is not a theorem"
  let changed := ConstantInfo.thmInfo {thm with type := mkConst ``True}
  expectRejected "changed theorem statement" <|
    compareAt challenge {solution with constMap := solution.constMap.insert first changed}
      (targets ++ legal) #[] primitives
  let areaName := `Research.DerivativeSwitch.Volume.area
  let some (.defnInfo area) := solution.constMap[areaName]?
    | throw <| IO.userError "Missing area definition"
  -- An unused let preserves meaning but changes the protected definition bytes.
  let changedArea := ConstantInfo.defnInfo {area with
    value := .letE `unused (mkConst ``Nat) (mkNatLit 0) area.value true}
  expectRejected "changed protected definition" <|
    compareAt challenge {solution with constMap := solution.constMap.insert areaName changedArea}
      (targets ++ legal) #[] primitives
  expectRejected "challenge holes as solution proofs" <|
    checkAxioms challenge targets #[] legal
