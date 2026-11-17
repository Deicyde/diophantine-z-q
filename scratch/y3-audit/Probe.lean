import ZInQKernel.OneProof.Main
open Lean Meta Elab Command

def cival (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

partial def y3closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      match env.find? c with
      | none => pure ()
      | some ci =>
        let ns0 := ci.type.getUsedConstants ++ ((cival ci).map (·.getUsedConstants) |>.getD #[])
        let ns := match ci with
          | .inductInfo ii => ns0 ++ ii.ctors.toArray
          | _ => ns0
        for n in ns do
          if !seen.contains n then stack := n :: stack
  return seen

def y3markers : List Name := [
  `LeafQM.AV.R1UnivRigid.R1fpPropsAb, `LeafQM.AV.R1fpProps, `LeafQM.AV.PtEquiv,
  `LeafQM.AV.R1UnivRigid.R1famAbProps, `LeafQM.AV.R1famProps,
  `LeafQM.AV.R1UnivRigid.R1univAbProps, `LeafQM.AV.R1univProps,
  `LeafQM.AV.R1UnivRigid.QMAbScheme, `LeafQM.AV.QMFamily, `LeafQM.AV.IsFibreOf,
  `RayClassCFT.ShimuraMainThmIDeligneY3AbU, `SGRSplit.ShimuraIntegralModelRep]


partial def collectFieldPt (e : Expr) (acc : Std.HashSet String) : Std.HashSet String :=
  match e with
  | .app f a =>
    let acc := collectFieldPt f (collectFieldPt a acc)
    if e.isAppOfArity `LeafQM.AV.fieldPt 3 then
      let k := e.getArg! 0
      let s := match k.getAppFn with
        | .const n _ => n.toString
        | .bvar _ => "<var>"
        | .fvar _ => "<var>"
        | _ => "<other>"
      acc.insert s
    else acc
  | .lam _ t b _ => collectFieldPt t (collectFieldPt b acc)
  | .forallE _ t b _ => collectFieldPt t (collectFieldPt b acc)
  | .letE _ t v b _ => collectFieldPt t (collectFieldPt v (collectFieldPt b acc))
  | .mdata _ b => collectFieldPt b acc
  | .proj _ _ b => collectFieldPt b acc
  | _ => acc

elab "#y3probe" : command => do
  let env ← getEnv
  let cl := y3closure env [`ZInQ.OneProof.frozenTarget]
  logInfo m!"closure size {cl.size}"
  logInfo m!"frozen value? {(env.find? `ZInQ.OneProof.frozenTarget).map (fun ci => (cival ci).isSome)}"
  logInfo m!"open58 in cl {cl.contains `HDec.HSyn.sixContactMin_of_open58}"
  for m in y3markers do
    logInfo m!"marker {m} in closure: {cl.contains m}"
  let mut out : Array String := #[]
  for c in cl.toList do
    match env.find? c with
    | none => pure ()
    | some ci =>
      let tys := ci.type.getUsedConstants
      let vs := (cival ci).map (·.getUsedConstants) |>.getD #[]
      let hitT := y3markers.filter (tys.contains ·)
      let hitV := y3markers.filter (vs.contains ·)
      if !(hitT.isEmpty && hitV.isEmpty) then
        let kind := match ci with | .thmInfo _ => "thm" | .defnInfo _ => "def" | _ => "other"
        let fT := (collectFieldPt ci.type {}).toList
        let fV := ((cival ci).map (fun v => (collectFieldPt v {}).toList)).getD []
        out := out.push s!"{c}\t{kind}\tT:{hitT.map (·.getString!)}\tV:{hitV.map (·.getString!)}\tfT:{fT}\tfV:{fV}"
  IO.FS.writeFile "scratch/y3-audit/probe_out.tsv" (String.intercalate "\n" (out.qsort (· < ·)).toList)
  logInfo m!"{out.size} hits"

#y3probe
