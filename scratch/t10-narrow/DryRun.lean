import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.T10NarrowChain
import Lean

/-! Generated top, with the base headline imported as a closure control. -/

theorem ZInQ.OneProof.frozenTarget_t10
    (r : HDec.HSyn.OpenResearchLeaves67) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves29_t10)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves) (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open86_t10 r t l)
    (ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing hRC hCT hB hK)

#print axioms ZInQ.OneProof.frozenTarget_t10

open Lean Elab Command Meta

-- Neither T10 proposition occurs in dependency packages of ZInQKernel.
private def inProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`ZInQKernel).isPrefixOf env.header.modules[i.toNat]!.module
  | none => true

private def projectClosure (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !inProject env n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      todo := todo ++ ci.type.getUsedConstants
      if let .inductInfo i := ci then todo := todo ++ i.ctors.toArray
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  return seen

private def checkClosure (env : Environment) (root : Name) (isLocal : Bool) : CommandElabM Unit := do
  unless (env.find? root).isSome do throwError "Missing {root}"
  let names := projectClosure env root
  let old := names.contains `T10Etale.T10_TateDuality
  let loc := names.contains `T10Etale.T10_TateDualityLocal
  logInfo m!"{root}: {names.size} project constants; old T10={old}, local T10={loc}"
  unless old == !isLocal && loc == isLocal do
    throwError "Unexpected Tate duality dependency"
  let axs ← collectAxioms root
  unless axs.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "Nonstandard axioms in {root}: {axs.toList}"

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  checkClosure env `HDec.HSyn.sixContactMin_of_open86 false
  checkClosure env `HDec.HSyn.sixContactMin_of_open86_t10 true
  checkClosure env `ZInQ.OneProof.frozenTarget false
  checkClosure env `ZInQ.OneProof.frozenTarget_t10 true

/-- Check that the type of every open entry except the rewritten field is identical. -/
private def openEntries (root : Name) : MetaM (Array (Name × Expr) × Nat) := do
  let env ← getEnv
  let ci ← getConstInfo root
  forallTelescope ci.type fun args _ => do
    unless args.size == 7 do throwError "Unexpected number of headline arguments"
    let mut out := #[]
    for arg in args.extract 0 3 do
      let ty ← inferType arg
      unless ty.isConst && isStructure env ty.constName! do throwError "Expected an H bundle"
      let s := ty.constName!
      for f in getStructureFields env s do
        let ci ← getConstInfo (s ++ f)
        let ty := ci.type.bindingBody!
        if ty.hasLooseBVars then throwError "Unexpected dependent bundle field {f}"
        out := out.push (f, ty)
    let hSize := out.size
    for arg in args.extract 3 args.size do
      out := out.push ((← arg.fvarId!.getUserName), (← inferType arg))
    return (out, hSize)

run_cmd liftTermElabM do
  let (old, oldH) ← openEntries `ZInQ.OneProof.frozenTarget
  let (new, newH) ← openEntries `ZInQ.OneProof.frozenTarget_t10
  unless oldH == 29 && newH == 29 && old.size == 33 && new.size == 33 do
    throwError "Unexpected open entry count"
  let mut changed := 0
  for ((f, ft), (g, gt)) in old.zip new do
    if f == `t10TateDuality then
      unless g == `t10TateDualityLocal && ft.isConstOf `T10Etale.T10_TateDuality &&
          gt.isConstOf `T10Etale.T10_TateDualityLocal do
        throwError "Wrong replacement for Tate duality"
      changed := changed + 1
    else
      unless f == g && ft == gt do throwError "Unexpected change in {f}"
  unless changed == 1 do throwError "Expected exactly one field replacement"
  logInfo m!"Open entries: {old.size} ({oldH} H) → {new.size} ({newH} H); only Tate duality changes."

-- This command still audits the unchanged base headline.
set_option maxHeartbeats 0 in
#discharges
