import ZInQKernel.OneProof.Main
import Lean

/-!
# Prune scan: fields of `ZInQ.OneProof.frozenTarget`'s bundles that no proof needs

Run from the repository root, after `lake build +ZInQKernel.OneProof.Main`:

    lake env lean scratch/one-proof/PruneScan.lean

A *bundle* is a `Prop`-valued structure declared in a `ZInQKernel.OneProof` module. Every
projection of a bundle field occurring in the closure of `frozenTarget` (types and values, proofs
included) is classified:

* if it is, directly, the `j`-th field argument of a bundle constructor `S'.mk`, it only threads the
  field into an older bundle: an edge `(S, i) → (S', j)`;
* otherwise it is a real use: `(S, i)` is USED.

A `casesOn`/`rec` on a bundle marks all of its fields USED (conservative). USED is then closed under
the edges backwards: `(S, i)` is used when it threads into a used field. The scan prints, for each
bundle in `frozenTarget`'s hypotheses, the fields that are not used: those can be removed from the
whole chain without changing any proof other than the bundle plumbing.
-/

open Lean

namespace PruneScan

def isOneProofModule (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => (`ZInQKernel.OneProof).isPrefixOf env.header.modules[idx.toNat]!.module
  | none => false

/-- `Prop`-valued structures declared in OneProof modules. -/
def isBundle (env : Environment) (s : Name) : Bool :=
  isStructure env s && isOneProofModule env s &&
    match env.find? s with
    | some (.inductInfo v) => Id.run do
        -- the structure lives in `Prop`: its type ends in `Sort 0`
        let mut t := v.type
        while t.isForall do t := t.bindingBody!
        return t == .sort .zero
    | _ => false

def constValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Constants reachable from `root` through types and values. -/
def closure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    out := out.push c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := constValue? ci then todo := todo ++ v.getUsedConstants
  return out

structure St where
  used : Std.HashSet (Name × Nat) := {}
  edges : Std.HashMap (Name × Nat) (Array (Name × Nat)) := {}  -- (S', j) ↦ sources (S, i)
  casesHits : Array Name := #[]
  seen : Std.HashSet Expr := {}

abbrev M := StateM St

def addUse (k : Name × Nat) : M Unit := modify fun s => { s with used := s.used.insert k }

def addEdge (src dst : Name × Nat) : M Unit :=
  modify fun s => { s with edges := s.edges.insert dst ((s.edges.getD dst #[]).push src) }

def record (env : Environment) (k : Name × Nat) (ctx : Option (Name × Nat)) : M Unit := do
  match ctx with
  | some dst => if isBundle env dst.1 then addEdge k dst else addUse k
  | none => addUse k

partial def visit (env : Environment) (e : Expr) (ctx : Option (Name × Nat)) : M Unit := do
  if ctx.isNone then
    if (← get).seen.contains e then return
    modify fun s => { s with seen := s.seen.insert e }
  match e with
  | .mdata _ b => visit env b ctx
  | .proj s i b =>
    if isBundle env s then record env (s, i) ctx
    visit env b none
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const fn _ =>
      if let some (.ctorInfo cv) := env.find? fn then
        if isBundle env cv.induct then
          for i in [:args.size] do
            visit env args[i]! (if i ≥ cv.numParams then some (cv.induct, i - cv.numParams) else none)
          return
      if let some pinfo := env.getProjectionFnInfo? fn then
        if let some (.ctorInfo cv) := env.find? pinfo.ctorName then
          if isBundle env cv.induct && args.size > pinfo.numParams then
            record env (cv.induct, pinfo.i) ctx
            for a in args do visit env a none
            return
      -- casesOn / rec on a bundle: every field counts as used
      match fn with
      | .str s last =>
        if (last == "casesOn" || last == "rec" || last == "recOn") && isBundle env s then
          modify fun st => { st with casesHits := st.casesHits.push s }
          if let some (.inductInfo iv) := env.find? s then
            if let some (.ctorInfo cv) := env.find? iv.ctors.head! then
              for j in [:cv.numFields] do addUse (s, j)
      | _ => pure ()
      for a in args do visit env a none
    | _ =>
      visit env f none
      for a in args do visit env a none
  | .lam _ t b _ | .forallE _ t b _ => do visit env t none; visit env b none
  | .letE _ t v b _ => do visit env t none; visit env v none; visit env b none
  | _ => pure ()

/-- Projection functions, constructors and the structure's own auxiliary constants are not uses. -/
def skip (env : Environment) (c : Name) : Bool :=
  (env.getProjectionFnInfo? c).isSome || (match env.find? c with
    | some (.ctorInfo _) | some (.recInfo _) => true
    | _ => false) ||
  (match c with
    | .str s _ => isBundle env s
    | _ => false)

def fieldNames (env : Environment) (s : Name) : Array Name :=
  getStructureFields env s

def visitConst (env : Environment) (ci : ConstantInfo) : M Unit := do
  visit env ci.type none
  if let some v := constValue? ci then visit env v none

end PruneScan

open PruneScan in
run_cmd do
  let env ← getEnv
  let root := `ZInQ.OneProof.frozenTarget
  let cl := closure env root
  let mut st : St := {}
  for c in cl do
    if skip env c then continue
    if let some ci := env.find? c then
      let ((), st') := (visitConst env ci).run st
      st := st'
  -- close USED backwards along the edges
  let mut used := st.used
  let mut todo := used.toArray
  while !todo.isEmpty do
    let k := todo.back!
    todo := todo.pop
    for src in st.edges.getD k #[] do
      if !used.contains src then
        used := used.insert src
        todo := todo.push src
  -- the bundles in frozenTarget's hypotheses
  let some ci := env.find? root | throwError "no {root}"
  let mut t := ci.type
  let mut tops : Array Name := #[]
  while t.isForall do
    if let .const s _ := t.bindingDomain!.getAppFn then
      if isBundle env s then tops := tops.push s
    t := t.bindingBody!
  logInfo m!"PRUNE closure={cl.size} directUses={st.used.size} edges={st.edges.size} casesOn={st.casesHits.size}"
  let mut total := 0
  for s in tops do
    let fs := fieldNames env s
    let mut unused : Array Name := #[]
    for j in [:fs.size] do
      if !used.contains (s, j) then unused := unused.push fs[j]!
    total := total + unused.size
    logInfo m!"PRUNE bundle {s}: {fs.size} fields, unused {unused.size}: {unused.toList}"
  logInfo m!"PRUNE total unused top-level fields: {total}"
