import ZInQKernel.Contrib.OneProof.RC.KappaRational2.Jacobian
import ZInQKernel.Contrib.OneProof.RC.KappaRational2.Consumers
import ZInQKernel.Contrib.OneProof.RC.KappaRational2.WeakWeil
import Lean

open Lean Elab Command

set_option maxHeartbeats 0

private def declarationModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.allImportedModuleNames[i.toNat]!
  | none => env.mainModule

-- Walk types and bodies, including the bodies of project theorems and opaque
-- constants. Stop at package boundaries: library files outside this project
-- cannot import downstream project modules.
private def projectClosure (env : Environment) (roots : Array Name) :
    CommandElabM (Std.HashSet Name) := do
  let projectModules := env.allImportedModuleNames.map fun m =>
    m.toString == "ZInQKernel" || m.toString.startsWith "ZInQKernel."
  let mut stack := roots
  let mut visited : Std.HashSet Name := {}
  let mut project : Std.HashSet Name := {}
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    if (env.getModuleIdxFor? n).any (fun i => projectModules[i.toNat]!) then
      project := project.insert n
      let some info := env.find? n | throwError "Missing project declaration: {n}"
      for dep in info.getUsedConstantsAsSet do
        stack := stack.push dep
  return project

private def forbidden (mod n : Name) : Bool :=
  let m := mod.toString
  let decl := (n.toString.splitOn ".").getLast!
  m.startsWith "ZInQKernel.Contrib.OneProof.RC.ParamJoin." ||
    (m.splitOn ".AtScale").length > 1 ||
    (decl.splitOn "AtScale").length > 1 ||
    (decl.splitOn "atScale").length > 1 ||
    n == `ZInQ.Manuscript.RC.KappaRational.algebraicParametrizationAtScale_iff ||
    n == `ZInQ.Manuscript.RC.ModFnField.coordinates_rationalLaurent ||
    n == `ZInQ.Manuscript.RC.ModFnField.coordinates_rationalTaylor

run_cmd do
  let env := (← getEnv).setExporting false
  if env.allImportedModuleNames.contains `ZInQKernel.OneProof.Main then
    throwError "Main was imported"
  logInfo "ZInQKernel.OneProof.Main absent from transitive imports."
  let roots := #[
      `ZInQ.Manuscript.RC.KappaRational2.scaled_periods_clear_lattice,
      `ZInQ.Manuscript.RC.KappaRational2.rational_of_reference_scale,
      `ZInQ.Manuscript.RC.KappaRational2.rational_of_matching_coeffs,
      `ZInQ.Manuscript.RC.KappaRational2.reference_scale_of_jacobian_values,
      `ZInQ.Manuscript.RC.KappaRational2.rational_of_jacobian_values,
      `ZInQ.Manuscript.RC.KappaRational2.newformPeriodsRational_of_modularToWeakWeil,
      `ZInQ.Manuscript.RC.KappaRational2.rational_of_modularToWeakWeil]
  let deps ← projectClosure env roots
  for root in roots do
    unless deps.contains root do
      throwError "Root absent from its own closure: {root}"
    logInfo m!"Checked root: {root}"
  unless deps.contains `ZInQ.Manuscript.RC.KappaRational.rational_of_projective_values_on_tail do
    throwError "Independent cusp coefficient comparison was not reached"
  let hits := deps.toArray.filter (fun n => forbidden (declarationModule env n) n)
  unless hits.isEmpty do
    throwError "Forbidden declarations in the proof closures: {hits}"
  logInfo m!"{deps.size} project declarations in the union of the closures; no ParamJoin or AtScale dependencies."

  -- Positive controls. Each consumer should use its old at-scale counterpart
  -- and independently call the already audited fixed-scale proof.
  let ns := `ZInQ.Manuscript.RC
  for (wr, base) in #[
      (`prepared_values_of_reference_scale, `ParamJoin.prepared_values),
      (`missing_values_of_reference_scale, `ParamJoin.missing_values),
      (`ring_values_of_reference_scale, `ParamJoin.ring_values),
      (`genus_values_of_reference_scale, `ParamJoin.genus_values),
      (`hElkikMD_of_reference_scale, `J0Cusps.hElkikMD_atScale)] do
    let root := ns ++ `KappaRational2 ++ wr
    let base := ns ++ base
    let some info := env.find? root | throwError "Missing consumer {root}"
    let deps := info.getUsedConstantsAsSet
    unless deps.contains base &&
        deps.contains `ZInQ.Manuscript.RC.KappaRational2.rational_of_matching_coeffs do
      throwError "{root} does not reach both expected inputs"
    logInfo m!"{root}: reaches {base} and the independently audited scale proof."
