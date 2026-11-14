import ZInQKernel.OneProof.Main
import Lean

/-!
# Prune scan: fields of `ZInQ.OneProof.frozenTarget`'s bundles that no proof needs

Run from the repository root, after `lake build +ZInQKernel.OneProof.Main`:

    lake env lean scratch/one-proof/PruneScan.lean

A *bundle* is a `Prop`-valued structure declared in a `ZInQKernel.OneProof` module. Every
projection of a bundle field occurring in the closure of `frozenTarget` (types and values, proofs
included) is classified:

* if it occurs anywhere inside the `j`-th field argument of a bundle constructor `S'.mk` (innermost
  constructor wins), it only feeds that field: an edge `(S, i) → (S', j)`;
* otherwise it is a real use: `(S, i)` is USED.

Each constant whose closure touches a bundle is visited once per context it is referenced from, so a
helper theorem used only inside a field argument feeds only that field.
A `casesOn`/`rec` on a bundle treats the field binders of its minor premise like projections
(all fields USED when the minor premise is not a lambda over every field). USED is then closed under
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
  seen : Std.HashSet (Expr × Option (Name × Nat)) := {}
  marks : Std.HashMap FVarId (Name × Nat) := {}  -- field binders of a `casesOn` minor premise
  nextMark : Nat := 0
  relevant : NameSet := {}  -- constants whose closure touches a bundle
  queue : Array (Name × Option (Name × Nat)) := #[]
  queued : Std.HashSet (Name × Option (Name × Nat)) := {}

abbrev M := StateM St

def addUse (k : Name × Nat) : M Unit := modify fun s => { s with used := s.used.insert k }

def addEdge (src dst : Name × Nat) : M Unit :=
  modify fun s => { s with edges := s.edges.insert dst ((s.edges.getD dst #[]).push src) }

def record (env : Environment) (k : Name × Nat) (ctx : Option (Name × Nat)) : M Unit := do
  match ctx with
  | some dst => if isBundle env dst.1 then addEdge k dst else addUse k
  | none => addUse k

/-- Visit `c`'s body later, under the context it is referenced from. -/
def enqueue (c : Name) (ctx : Option (Name × Nat)) : M Unit := do
  let st ← get
  if st.relevant.contains c && !st.queued.contains (c, ctx) then
    set { st with queue := st.queue.push (c, ctx), queued := st.queued.insert (c, ctx) }

partial def visit (env : Environment) (e : Expr) (ctx : Option (Name × Nat)) : M Unit := do
  if (← get).seen.contains (e, ctx) then return
  modify fun s => { s with seen := s.seen.insert (e, ctx) }
  match e with
  | .mdata _ b => visit env b ctx
  | .proj s i b =>
    if isBundle env s then record env (s, i) ctx
    visit env b ctx
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const fn _ =>
      enqueue fn ctx
      if let some (.ctorInfo cv) := env.find? fn then
        if isBundle env cv.induct then
          for i in [:args.size] do
            visit env args[i]! (if i ≥ cv.numParams then some (cv.induct, i - cv.numParams) else ctx)
          return
      if let some pinfo := env.getProjectionFnInfo? fn then
        if let some (.ctorInfo cv) := env.find? pinfo.ctorName then
          if isBundle env cv.induct && args.size > pinfo.numParams then
            record env (cv.induct, pinfo.i) ctx
            for a in args do visit env a ctx
            return
      -- casesOn / rec on a bundle: follow the minor premise's field binders as if they were
      -- projections; if the minor premise is not a lambda over all fields, every field is used
      match fn with
      | .str s last =>
        if (last == "casesOn" || last == "rec" || last == "recOn") && isBundle env s then
          modify fun st => { st with casesHits := st.casesHits.push s }
          if let some (.inductInfo iv) := env.find? s then
            if let some (.ctorInfo cv) := env.find? iv.ctors.head! then
              let idx := if last == "rec" then cv.numParams + 1 else cv.numParams + 2
              let minor := if h : idx < args.size then some args[idx] else none
              match minor with
              | some m =>
                if m.getNumHeadLambdas ≥ cv.numFields then
                  let mut b := m
                  for j in [:cv.numFields] do
                    visit env b.bindingDomain! ctx
                    let st ← get
                    let id : FVarId := ⟨.mkNum `_pruneMark st.nextMark⟩
                    set { st with marks := st.marks.insert id (s, j), nextMark := st.nextMark + 1 }
                    b := b.bindingBody!.instantiate1 (.fvar id)
                  visit env b ctx
                  for i in [:args.size] do
                    if i != idx then visit env args[i]! ctx
                  return
                else
                  for j in [:cv.numFields] do addUse (s, j)
              | none => for j in [:cv.numFields] do addUse (s, j)
      | _ => pure ()
      for a in args do visit env a ctx
    | _ =>
      visit env f ctx
      for a in args do visit env a ctx
  | .lam _ t b _ | .forallE _ t b _ => do visit env t ctx; visit env b ctx
  | .letE _ t v b _ => do visit env t ctx; visit env v ctx; visit env b ctx
  | .fvar id => do
    if let some k := (← get).marks[id]? then record env k ctx
  | .const c _ => enqueue c ctx
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

def visitConst (env : Environment) (ci : ConstantInfo) (ctx : Option (Name × Nat)) : M Unit := do
  visit env ci.type ctx
  if let some v := constValue? ci then visit env v ctx

/-- Seeds of `relevant`: a bundle, a constant in a bundle's namespace (its constructor, projections,
recursors), or a body with a raw bundle projection. -/
def touchesBundle (env : Environment) (c : Name) : Bool :=
  isBundle env c || isBundle env c.getPrefix ||
  (match env.find? c with
    | some ci => ((constValue? ci).bind fun v => v.find? fun
        | .proj s _ _ => isBundle env s
        | _ => false).isSome
    | none => false)

/-- Process the queue: each relevant constant once per context it is referenced from. -/
def drain (env : Environment) : M Unit := do
  repeat
    let st ← get
    if st.queue.isEmpty then break
    let (c, ctx) := st.queue.back!
    set { st with queue := st.queue.pop }
    if !skip env c then
      if let some ci := env.find? c then visitConst env ci ctx

end PruneScan

open PruneScan in
run_cmd do
  let env ← getEnv
  let root := `ZInQ.OneProof.frozenTarget
  let cl := closure env root
  -- relevant = constants of the closure from which a bundle seed is reachable
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut relevant : NameSet := {}
  let mut todo : Array Name := #[]
  for c in cl do
    if let some ci := env.find? c then
      let deps := ci.type.getUsedConstants ++ ((constValue? ci).map (·.getUsedConstants)).getD #[]
      for d in deps do rev := rev.insert d ((rev.getD d #[]).push c)
    if touchesBundle env c then
      relevant := relevant.insert c
      todo := todo.push c
  while !todo.isEmpty do
    let d := todo.back!
    todo := todo.pop
    for c in rev.getD d #[] do
      if !relevant.contains c then
        relevant := relevant.insert c
        todo := todo.push c
  let st0 : St := { relevant }
  let ((), st) := (do enqueue root none; drain env).run st0
  -- close USED backwards along the edges
  let mut used := st.used
  let mut work := used.toArray
  while !work.isEmpty do
    let k := work.back!
    work := work.pop
    for src in st.edges.getD k #[] do
      if !used.contains src then
        used := used.insert src
        work := work.push src
  -- the bundles in frozenTarget's hypotheses
  let some ci := env.find? root | throwError "no {root}"
  let mut t := ci.type
  let mut tops : Array Name := #[]
  while t.isForall do
    if let .const s _ := t.bindingDomain!.getAppFn then
      if isBundle env s then tops := tops.push s
    t := t.bindingBody!
  logInfo m!"PRUNE closure={cl.size} relevant={relevant.size} visits={st.queued.size} directUses={st.used.size} edges={st.edges.size} casesOn={st.casesHits.size} {st.casesHits.toList}"
  let mut total := 0
  for s in tops do
    let fs := fieldNames env s
    let mut unused : Array Name := #[]
    for j in [:fs.size] do
      if !used.contains (s, j) then unused := unused.push fs[j]!
    total := total + unused.size
    logInfo m!"PRUNE bundle {s}: {fs.size} fields, unused {unused.size}: {unused.toList}"
  logInfo m!"PRUNE total unused top-level fields: {total}"
