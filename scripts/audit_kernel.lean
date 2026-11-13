import Lean
import Lean.Replay

/- Run as a separate process after building the submitted modules. Do not import
   candidate modules into this executable or execute their initializers. -/
open Lean

def checked {α : Type} (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def field (j : Json) (k : String) : IO Json := checked (j.getObjVal? k)
def stringField (j : Json) (k : String) : IO String := do
  checked ((← field j k).getStr?)

def prettyType (env : Environment) (e : Expr) : IO String := do
  let (f, _, _) ← (Meta.ppExpr e).toIO
    { fileName := "<kernel-audit>", fileMap := default,
      options := ({} : Options).set `pp.width (120 : Nat) } { env }
  return f.pretty

-- Walk actual bodies, including opaque bodies, instead of trusting an imported
-- cached axiom summary. A global visited set keeps this linear in the closure.
partial def auditClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (axioms : NameSet := {}) : IO NameSet := do
  match todo with
  | [] => return axioms
  | n :: rest =>
    if seen.contains n then return ← auditClosure env rest seen axioms
    let some ci := env.find? n | throw (IO.userError s!"Missing dependency {n}")
    let mut ax := axioms
    if ci.isAxiom then
      unless n == `propext || n == `Quot.sound || n == `Classical.choice do
        throw (IO.userError s!"Forbidden axiom {n}")
      ax := ax.insert n
    auditClosure env (ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n) ax

def exactType (env : Environment) (proof : Name) (expected : Expr) : IO Unit := do
  let some ci := env.find? proof | throw (IO.userError s!"Missing proof {proof}")
  unless ci.levelParams.isEmpty do
    throw (IO.userError s!"Unexpected universe parameters on {proof}")
  match ci with
  | .thmInfo _ => pure ()
  | .defnInfo _ =>
    if ci.isUnsafe || ci.isPartial then throw (IO.userError s!"Unsafe/partial proof {proof}")
  | _ => throw (IO.userError s!"Expected a theorem or definition with proof body: {proof}")
  match Kernel.isDefEq env {} ci.type expected with
  | .ok true => pure ()
  | _ => throw (IO.userError s!"Wrong full type of {proof}. Additional hypotheses are not allowed.")

-- Lean may realize the same auxiliary theorem independently in several modules.
-- Importing merges matching theorem signatures, but their proof bodies may differ.
def sameTheoremSignature (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo x, .thmInfo y =>
    x.name == y.name && x.type == y.type &&
      x.levelParams == y.levelParams && x.all == y.all
  | _, _ => false

-- Replay deliberately skips a theorem already present with the same signature.
-- Check each raw duplicate body separately, under an unused name, so importing
-- cannot hide an invalid body behind another module's copy.
def checkDuplicateBody (env : Kernel.Environment) (ci : ConstantInfo) (i : Nat) : IO Unit := do
  let .thmInfo info := ci |
    throw (IO.userError s!"Non-theorem duplicate {ci.name}")
  let mut j := i
  let mut fresh := Name.num `_kernelAuditDuplicate j
  while (env.find? fresh).isSome do
    j := j + 1
    fresh := Name.num `_kernelAuditDuplicate j
  let decl := Declaration.thmDecl { info with name := fresh, all := [fresh] }
  match env.addDeclCore 0 0 decl (cancelTk? := none) with
  | .ok _ => pure ()
  | .error e =>
    throw (IO.userError s!"Invalid duplicate theorem body {ci.name}: {← e.toMessageData {} |>.toString}")

def main (args : List String) : IO Unit := do
  let [specPath, outputPath] := args |
    throw (IO.userError "usage: audit_kernel SPEC.json REPORT.json")
  let spec ← checked (Json.parse (← IO.FS.readFile specPath))
  let modules ← (← checked ((← field spec "modules").getArr?)).mapM fun x => do
    return (← checked x.getStr?).toName
  unless !modules.isEmpty do throw (IO.userError "Empty module list")
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun m => { module := m, importAll := true }) {}
  let mut owned : Std.HashMap Name ConstantInfo := {}
  let mut rawOwned : Array ConstantInfo := #[]
  let mut duplicates : NameSet := {}
  let mut roots : NameSet := {}
  let mut external : NameSet := {}
  let mut found : NameSet := {}
  for i in [:env.header.modules.size] do
    let m := env.header.modules[i]!.module
    if modules.contains m then
      found := found.insert m
      let data := env.header.moduleData[i]!
      unless data.constNames.size == data.constants.size do
        throw (IO.userError s!"Malformed declaration table in {m}")
      for n in data.constNames, ci in data.constants do
        unless n == ci.name do
          throw (IO.userError s!"Mismatched declaration name in {m}: {n}")
      for imp in data.imports do
        unless modules.contains imp.module do external := external.insert imp.module
      for ci in data.constants do
        let n := ci.name
        rawOwned := rawOwned.push ci
        -- Read the serialized body, not env.find?, which can select a different
        -- module's duplicate. Include every raw body's dependency roots.
        if ci.isAxiom && n != `propext && n != `Quot.sound && n != `Classical.choice then
          throw (IO.userError s!"Forbidden axiom {n}")
        for dep in ci.getUsedConstantsAsSet do roots := roots.insert dep
        roots := roots.insert n
        if let some previous := owned[n]? then
          unless sameTheoremSignature previous ci do
            throw (IO.userError s!"Incompatible project declaration copies: {n}")
          duplicates := duplicates.insert n
        owned := owned.insert n ci
  for m in modules do
    unless found.contains m do throw (IO.userError s!"Module not imported: {m}")
  let base ← importModules (external.toArray.map fun m => { module := m, importAll := true }) {}
  for imported in base.header.modules do
    if modules.contains imported.module then
      throw (IO.userError s!"Project module leaked into external base: {imported.module}")
  for (n, ci) in owned.toList do
    if let some existing := base.find? n then
      unless sameTheoremSignature existing ci do
        throw (IO.userError s!"Incompatible declaration in external base: {n}")
      duplicates := duplicates.insert n
  -- This checks project declarations even on a root build-cache hit.
  let replayed ← base.toKernelEnv.replay owned
  let mut duplicateBodies := 0
  for ci in rawOwned do
    if duplicates.contains ci.name then
      checkDuplicateBody replayed ci duplicateBodies
      duplicateBodies := duplicateBodies + 1
  let verified := Environment.ofKernelEnv replayed
  let axioms ← auditClosure env roots.toList
  let headline ← field spec "headline"
  let headlineName := (← stringField headline "declaration").toName
  let expectedName := (← stringField headline "type_declaration").toName
  let some expected := verified.find? expectedName |
    throw (IO.userError s!"Missing pinned headline type {expectedName}")
  exactType verified headlineName expected.type
  let exports ← checked ((← field spec "exports").getArr?)
  for e in exports do
    let n := (← checked e.getStr?).toName
    unless owned.contains n do throw (IO.userError s!"Missing project export {n}")
  let mut results : Array Json := #[]
  for t in (← checked ((← field spec "targets").getArr?)) do
    let n := (← stringField t "declaration").toName
    let p := (← stringField t "provider").toName
    let some ci := verified.find? n | throw (IO.userError s!"Missing target {n}")
    unless ci.levelParams.isEmpty && ci.type == .sort .zero do
      throw (IO.userError s!"Target {n} must be a closed Prop declaration")
    let mut status := "open"
    if env.contains p then
      unless owned.contains p do throw (IO.userError s!"Provider not owned by project: {p}")
      exactType verified p (.const n [])
      status := "proved_exact_type"
    results := results.push (Json.mkObj [
      ("declaration", toJson n.toString), ("provider", toJson p.toString),
      ("status", toJson status),
      ("type", toJson (← prettyType env (ci.value?.getD (.const n []))))])
  let some headlineInfo := verified.find? headlineName |
    throw (IO.userError "Missing headline after replay")
  let skipped := owned.toList.filter fun (_, c) => c.isUnsafe || c.isPartial
  let report := Json.mkObj [
    ("schema", toJson "kernel-audit/v1"), ("status", toJson "passed"),
    ("modules", toJson (modules.map Name.toString)),
    ("declarations", toJson owned.size),
    ("raw_declaration_occurrences", toJson rawOwned.size),
    ("duplicate_theorem_bodies_rechecked", toJson duplicateBodies),
    ("runtime_declarations_not_replayed", toJson (skipped.map fun (n, _) => n.toString)),
    ("allowed_axioms_used", toJson (axioms.toList.map Name.toString)),
    ("headline", toJson headlineName.toString),
    ("headline_type", toJson (← prettyType env headlineInfo.type)),
    ("targets", Json.arr results), ("protocol_acceptance", toJson false)]
  IO.FS.writeFile outputPath (report.pretty ++ "\n")
  IO.println s!"Kernel audit passed: {modules.size} modules, {owned.size} declarations"
