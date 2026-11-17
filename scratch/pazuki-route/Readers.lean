import ZInQKernel.OneProof.Main
import Lean
/-! pazuki-route: single-pass reader scan (replacement for the field taint, which did not finish in 2 h).
Lists every constant of the environment whose type or value uses a projection named `pazukiCor13Upper` of a bundle
structure, the field's type `ZInQ.HeightSplit.PazukiCor13Upper`, or `ZInQ.HeightSplit.r22_of_upper`. -/
open Lean

run_cmd do
  let env ← getEnv
  let targets : NameSet := NameSet.empty
    |>.insert `ZInQ.HeightSplit.PazukiCor13Upper |>.insert `ZInQ.HeightSplit.r22_of_upper
  let isProj : Name → Bool := fun n =>
    match env.getProjectionFnInfo? n, n with
    | some _, .str _ "pazukiCor13Upper" => true
    | _, _ => false
  let mut hits : Array String := #[]
  for (c, ci) in env.constants.map₁.toList do
    let v := match ci with
      | .defnInfo d => some d.value | .thmInfo t => some t.value | _ => none
    let us := (v.map Expr.getUsedConstants).getD #[]
    let bad := us.filter (fun u => targets.contains u || isProj u)
    if !bad.isEmpty then hits := hits.push s!"{c} USES {bad.toList}"
  for h in hits.qsort (· < ·) do IO.println h
  IO.println s!"{hits.size} readers"
