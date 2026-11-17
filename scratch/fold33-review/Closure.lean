import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges

/-!
# fold33-review: closure and hypothesis checks for the staged fold wip/leaf-fold33b (667e0aed)

1. The open hypotheses of `ZInQ.OneProof.frozenTarget` (as `#discharges` reads them), written with their full types
   to `scratch/fold33-review/open-statements.json` (a copy of `scripts/one_proof/OpenStatements.lean` with another
   output path).
2. The constant closure of `frozenTarget` (through values of definitions and proofs of theorems), searched for the
   removed Props and their known variants.
3. The *statement closure* of every open hypothesis: the constants its type reaches through definitions only
   (no theorem proofs). A removed Prop reached there would mean that a hypothesis restates it.
4. `#print axioms ZInQ.OneProof.frozenTarget`.
-/

open Lean Elab Command Meta ZInQ.OneProof.Discharges

/-- Constants reached from `root` through types and values (definitions and theorems). -/
partial def closureOf (env : Environment) (roots : Array Name) (followThm : Bool) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots.toList
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let mut cs := ci.type.getUsedConstants
      match ci with
      | .defnInfo d => cs := cs ++ d.value.getUsedConstants
      | .thmInfo t => if followThm then cs := cs ++ t.value.getUsedConstants
      | .opaqueInfo o => cs := cs ++ o.value.getUsedConstants
      | .inductInfo i => cs := cs ++ i.ctors.toArray
      | .ctorInfo c => cs := cs.push c.induct
      | _ => pure ()
      for c in cs do
        unless seen.contains c do stack := c :: stack
  return seen

def removedPatterns : List String :=
  ["SGA3_VIB_3_10", "MumfordGroupLawConn", "HomFreeFiniteAlgClosed", "HomFreeFinite",
   "GrossZagierHeegner", "NeronSchemeExtensionExists", "ShimuraMainCM", "GrossZagierModuliOpt",
   "sga3_VIB_3_10", "mumfordGroupLawConn", "homFreeFinite"]

def strContains (s pat : String) : Bool := (s.splitOn pat).length > 1

run_cmd do
  let env ← getEnv
  -- 1. open hypotheses
  let hyps ← liftTermElabM openHyps
  let mut entries : Array Json := #[]
  for h in hyps do
    let full ← liftTermElabM do
      let fmt ← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr h.type)
      pure (toString fmt)
    entries := entries.push <| Json.mkObj [("label", Json.str h.label), ("type", Json.str full)]
  IO.FS.writeFile "scratch/fold33-review/open-statements.json"
    ((Json.mkObj [("count", toJson entries.size), ("hypotheses", Json.arr entries)]).pretty ++ "\n")
  logInfo m!"OPEN: {entries.size} open hypotheses"
  for h in hyps do
    logInfo m!"HYP {h.label} : {h.type.getAppFn.constName?}"
  -- 2. full closure of frozenTarget
  let cl := closureOf env #[`ZInQ.OneProof.frozenTarget] true
  logInfo m!"CLOSURE size: {cl.size}"
  let mut hits : Array String := #[]
  for n in cl.toList do
    let s := n.toString
    for p in removedPatterns do
      if strContains s p then hits := hits.push s
  logInfo m!"CLOSURE hits ({hits.size}): {hits.qsort (· < ·)}"
  -- 3. statement closure of each open hypothesis
  for h in hyps do
    let roots := h.type.getUsedConstants
    let scl := closureOf env roots false
    let mut shits : Array String := #[]
    for n in scl.toList do
      let s := n.toString
      for p in removedPatterns do
        if strContains s p then shits := shits.push s
    unless shits.isEmpty do
      logInfo m!"STATEMENT-CLOSURE {h.label}: {shits.qsort (· < ·)}"
  logInfo m!"STATEMENT-CLOSURE check done"

#print axioms ZInQ.OneProof.frozenTarget
