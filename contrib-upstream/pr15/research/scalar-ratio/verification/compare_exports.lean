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

def expectedNames : Array String := #[
  "Research.DerivativeSwitch.finite_kernel_line",
  "Research.DerivativeSwitch.singular_kernel_line",
  "Research.DerivativeSwitch.boundary_images_meet_zero",
  "Research.DerivativeSwitch.no_identity_strict_square",
  "Research.DerivativeSwitch.Volume.area_action",
  "Research.DerivativeSwitch.Volume.area_neg_one",
  "Research.BoundaryScalar.adjugate_singularNormal",
  "Research.BoundaryScalar.adjugate_finiteNormal",
  "Research.BoundaryScalar.tensor_of_normal_form",
  "Research.BoundaryScalar.finite_tensor",
  "Research.BoundaryScalar.singular_tensor",
  "Research.BoundaryScalar.finite_cross_ne_zero",
  "Research.BoundaryScalar.singular_cross_ne_zero",
  "Research.BoundaryScalar.finite_coordinate_iff",
  "Research.BoundaryScalar.singular_coordinate_iff",
  "Research.BoundaryScalar.boundary_scalar_formula",
  "Research.BoundaryScalar.scalar_comparison",
  "Research.BoundaryScalar.normalized_scalar_comparison",
  "Research.BoundaryScalar.scalar_comparison_of_unit",
  "Research.BoundaryCupAdapter.cross_evaluations_eq",
  "Research.BoundaryCupAdapter.cross_evaluations_with_factors",
  "Research.DerivativeSwitch.ScalarRatio.coordinate_of_frame",
  "Research.DerivativeSwitch.ScalarRatio.coordinate_of_closed_frame",
  "Research.DerivativeSwitch.ScalarRatio.adjugate_ne_zero_of_frame",
  "Research.DerivativeSwitch.ScalarRatio.coordinate_unique",
  "Research.DerivativeSwitch.ScalarRatio.raw_side_coordinate",
  "Research.DerivativeSwitch.ScalarRatio.common_strict_coordinate_formula",
  "Research.DerivativeSwitch.ScalarRatio.CommonStrictData.coordinate_values",
  "Research.DerivativeSwitch.ScalarRatio.transported_ratio",
  "Research.DerivativeSwitch.ScalarRatio.transported_unit_criterion",
  "Research.DerivativeSwitch.ScalarRatio.integral_unit_criterion",
  "Research.DerivativeSwitch.ScalarRatio.CommonStrictData.actual_coordinate_ratio",
  "Research.DerivativeSwitch.ScalarRatio.CommonStrictData.actual_integral_unit_criterion",
  "Research.DerivativeSwitch.ScalarRatio.boundary_cup_cross_evaluations",
  "Research.DerivativeSwitch.ScalarRatio.normalization_defect",
  "Research.DerivativeSwitch.ScalarRatio.common_normalization_adapter",
  "Research.DerivativeSwitch.ScalarRatio.det_neg_one_common_normalization",
  "Research.DerivativeSwitch.ScalarRatio.integral_boundary_cup_adapter",
  "Research.DerivativeSwitch.ScalarRatio.valuation_equal_of_unitRelated"]

def main (args : List String) : IO Unit := do
  let [configPath, challengePath, solutionPath] := args
    | throw <| IO.userError "Expected config, challenge export, solution export"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile configPath)
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let allowed ← IO.ofExcept <| config.getObjValAs? (Array String) "permitted_axioms"
  let definitions ← IO.ofExcept <| config.getObjValAs? (Array String) "definition_names"
  unless names == expectedNames && definitions.isEmpty do
    throw <| IO.userError "Expected exact 39-name frozen inventory and no definition holes"
  let targets := names.map String.toName
  let legal := allowed.map String.toName
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  IO.ofExcept <| compareAt challenge solution (targets ++ legal) #[] primitives
  IO.ofExcept <| checkAxioms solution targets #[] legal

  -- Exercise real failure paths using only in-memory copies of the export.
  let first := `Research.BoundaryScalar.boundary_scalar_formula
  expectRejected "missing theorem" <|
    compareAt challenge {solution with constMap := solution.constMap.erase first}
      (targets ++ legal) #[] primitives
  let some (.thmInfo thm) := solution.constMap[first]?
    | throw <| IO.userError "Target is not a theorem"
  let changed := ConstantInfo.thmInfo {thm with type := mkConst ``True}
  expectRejected "changed theorem statement" <|
    compareAt challenge {solution with constMap := solution.constMap.insert first changed}
      (targets ++ legal) #[] primitives
  let normalName := `Research.BoundaryScalar.finiteNormal
  let some (.defnInfo normal) := solution.constMap[normalName]?
    | throw <| IO.userError "Missing finite normal-form definition"
  -- An unused let preserves meaning but changes the protected definition bytes.
  let changedNormal := ConstantInfo.defnInfo {normal with
    value := .letE `unused (mkConst ``Nat) (mkNatLit 0) normal.value true}
  expectRejected "changed protected definition" <|
    compareAt challenge {solution with constMap := solution.constMap.insert normalName changedNormal}
      (targets ++ legal) #[] primitives
  let rawName := `Research.DerivativeSwitch.ScalarRatio.common_strict_coordinate_formula
  expectRejected "missing raw common-strict theorem" <|
    compareAt challenge {solution with constMap := solution.constMap.erase rawName}
      (targets ++ legal) #[] primitives
  let unitName := `Research.DerivativeSwitch.ScalarRatio.UnitRelated
  let some (.defnInfo integralUnit) := solution.constMap[unitName]?
    | throw <| IO.userError "Missing integral-unit definition"
  let changedUnit := ConstantInfo.defnInfo {integralUnit with
    value := .letE `unused (mkConst ``Nat) (mkNatLit 0) integralUnit.value true}
  expectRejected "changed protected integral-unit definition" <|
    compareAt challenge {solution with constMap := solution.constMap.insert unitName changedUnit}
      (targets ++ legal) #[] primitives

  expectRejected "challenge holes as solution proofs" <|
    checkAxioms challenge targets #[] legal

  IO.println "STRUCTURE_AND_AXIOMS_PASS declarations=39 negative_controls=6; no kernel replay or isolation"
