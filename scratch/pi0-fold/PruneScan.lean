import ZInQKernel.OneProof.Main
import Lean

/-!
# Prune scan: fields of `ZInQ.OneProof.frozenTarget`'s bundles that no proof needs

Run from the repository root, after `lake build +ZInQKernel.OneProof.Main`:

    lake env lean scratch/pi0-fold/PruneScan.lean

A *bundle* is a `Prop`-valued structure declared in a `ZInQKernel.OneProof` module. The scan builds a
dependency graph whose nodes are bundle fields `(S, i)` and constants `c`, and an edge `a → b` means
"`a` is needed if `b` is". Each constant of `frozenTarget`'s closure whose own closure touches a
bundle is visited once; inside it, the current context is the constant itself, or the field `(S', j)`
while inside the `j`-th field argument of a bundle constructor `S'.mk` (innermost constructor wins).

* a projection of `(S, i)` gives `(S, i) → context`;
* a reference to a constant `d` gives `d → context`;
* a `casesOn`/`rec` on a bundle treats the field binders of its minor premise like projections (all
  fields, when the minor premise is not a lambda over every field).

`frozenTarget` is used; USED is closed backwards along the edges. The scan prints, for each bundle in
`frozenTarget`'s hypotheses, the fields that are not used: those can be removed from the whole chain
without changing any proof other than the bundle plumbing, and writes every field with its type and
verdict to `scratch/pi0-fold/used-fields.txt`.
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

inductive Node where
  | field (s : Name) (i : Nat)
  | const (c : Name)
  deriving BEq, Hashable, Inhabited

structure St where
  edges : Std.HashMap Node (Array Node) := {}  -- b ↦ the nodes a with a → b
  casesHits : Array Name := #[]
  seen : Std.HashSet (Expr × Node) := {}
  marks : Std.HashMap FVarId (Name × Nat) := {}  -- field binders of a `casesOn` minor premise
  nextMark : Nat := 0

abbrev M := StateM St

def addEdge (src dst : Node) : M Unit :=
  modify fun s => { s with edges := s.edges.insert dst ((s.edges.getD dst #[]).push src) }

partial def visit (env : Environment) (e : Expr) (ctx : Node) : M Unit := do
  if (← get).seen.contains (e, ctx) then return
  modify fun s => { s with seen := s.seen.insert (e, ctx) }
  match e with
  | .mdata _ b => visit env b ctx
  | .proj s i b =>
    if isBundle env s then addEdge (.field s i) ctx
    visit env b ctx
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const fn _ =>
      addEdge (.const fn) ctx
      if let some (.ctorInfo cv) := env.find? fn then
        if isBundle env cv.induct then
          for i in [:args.size] do
            visit env args[i]! (if i ≥ cv.numParams then .field cv.induct (i - cv.numParams) else ctx)
          return
      if let some pinfo := env.getProjectionFnInfo? fn then
        if let some (.ctorInfo cv) := env.find? pinfo.ctorName then
          if isBundle env cv.induct && args.size > pinfo.numParams then
            addEdge (.field cv.induct pinfo.i) ctx
            for a in args do visit env a ctx
            return
      -- casesOn / rec on a bundle: follow the minor premise's field binders as if they were
      -- projections; if the minor premise is not a lambda over all fields, every field is needed
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
                  for j in [:cv.numFields] do addEdge (.field s j) ctx
              | none => for j in [:cv.numFields] do addEdge (.field s j) ctx
      | _ => pure ()
      for a in args do visit env a ctx
    | _ =>
      visit env f ctx
      for a in args do visit env a ctx
  | .lam _ t b _ | .forallE _ t b _ => do visit env t ctx; visit env b ctx
  | .letE _ t v b _ => do visit env t ctx; visit env v ctx; visit env b ctx
  | .fvar id => do
    if let some (s, j) := (← get).marks[id]? then addEdge (.field s j) ctx
  | .const c _ => do
    addEdge (.const c) ctx
    -- an unapplied projection function still reads its field
    if let some pinfo := env.getProjectionFnInfo? c then
      if let some (.ctorInfo cv) := env.find? pinfo.ctorName then
        if isBundle env cv.induct then addEdge (.field cv.induct pinfo.i) ctx
  | _ => pure ()

/-- Projection functions, constructors, recursors and a bundle's generated auxiliaries (`casesOn`,
`recOn`, `noConfusion`, ...) are not uses. Theorems a file declares in a bundle's namespace (say
`TextbookLeaves.belyiX1`) are ordinary constants and are visited. -/
def skip (env : Environment) (c : Name) : Bool :=
  (env.getProjectionFnInfo? c).isSome || (match env.find? c with
    | some (.ctorInfo _) | some (.recInfo _) => true
    | _ => false) ||
  ((isBundle env c.getPrefix) && (isAuxRecursor env c || isNoConfusion env c ||
    (match c with
      | .str _ last => last == "ctorIdx" || last == "noConfusionType" || last.startsWith "match_"
      | _ => false)))

def fieldNames (env : Environment) (s : Name) : Array Name :=
  getStructureFields env s

/-- Seeds of the relevant constants: a bundle, a constant in a bundle's namespace (its constructor,
projections, recursors), or a body with a raw bundle projection. -/
def touchesBundle (env : Environment) (c : Name) : Bool :=
  isBundle env c || isBundle env c.getPrefix ||
  (match env.find? c with
    | some ci => ((constValue? ci).bind fun v => v.find? fun
        | .proj s _ _ => isBundle env s
        | _ => false).isSome
    | none => false)

end PruneScan

open PruneScan in
run_cmd do
  let env ← getEnv
  let root := `ZInQ.OneProof.frozenTarget
  let cl := closure env root
  -- relevant = constants of the closure from which a bundle seed is reachable (post-order DFS)
  let deps (c : Name) : Array Name := match env.find? c with
    | some ci => ci.type.getUsedConstants ++ ((constValue? ci).map (·.getUsedConstants)).getD #[]
    | none => #[]
  let mut memo : Std.HashMap Name Bool := {}
  let mut stack : Array (Name × Bool) := #[(root, false)]
  while !stack.isEmpty do
    let (c, done) := stack.back!
    stack := stack.pop
    if memo.contains c then continue
    if done then
      memo := memo.insert c (touchesBundle env c || (deps c).any fun d => memo.getD d false)
    else
      stack := stack.push (c, true)
      for d in deps c do
        if !memo.contains d then stack := stack.push (d, false)
  let relevant : NameSet := memo.fold (fun acc c r => if r then acc.insert c else acc) {}
  let mut st : St := {}
  let mut visited := 0
  for c in cl do
    if !relevant.contains c || skip env c then continue
    if let some ci := env.find? c then
      visited := visited + 1
      let act : M Unit := do
        visit env ci.type (.const c)
        if let some v := constValue? ci then visit env v (.const c)
      let ((), st') := act.run st
      st := st'
  -- close USED backwards along the edges, from frozenTarget
  let mut used : Std.HashSet Node := ({} : Std.HashSet Node).insert (.const root)
  let mut work : Array Node := #[.const root]
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
  logInfo m!"PRUNE closure={cl.size} relevant={relevant.size} visited={visited} edgeTargets={st.edges.size} used={used.size} casesOn={st.casesHits.size} {st.casesHits.toList}"
  let mut total := 0
  let mut lines : Array String := #[s!"# frozenTarget's bundle fields, USED or UNUSED (scratch/pi0-fold/PruneScan.lean)", ""]
  for s in tops do
    let fs := fieldNames env s
    let mut unused : Array Name := #[]
    lines := lines.push s!"## {s}"
    for j in [:fs.size] do
      let isUsed := used.contains (.field s j)
      if !isUsed then unused := unused.push fs[j]!
      -- the field's type, read off its projection function
      let ty ← match env.find? (s ++ fs[j]!) with
        | some ci => do
          let mut ft := ci.type
          while ft.isForall do ft := ft.bindingBody!
          let fmt ← Lean.Elab.Command.liftTermElabM <| Meta.ppExpr (if ft.hasLooseBVars then ci.type else ft)
          pure ((toString fmt).replace "\n" " ")
        | none => pure "?"
      lines := lines.push s!"{if isUsed then "USED  " else "UNUSED"} {fs[j]!} : {ty}"
    lines := lines.push ""
    total := total + unused.size
    logInfo m!"PRUNE bundle {s}: {fs.size} fields, unused {unused.size}: {unused.toList}"
  IO.FS.writeFile "scratch/pi0-fold/used-fields.txt" ("\n".intercalate lines.toList ++ "\n")
  logInfo m!"PRUNE total unused top-level fields: {total}"
  -- every bundle of the chain: a removed top field also removes the older fields it alone feeds
  let mut all : Array String := #[]
  for (c, _) in env.constants.toList do
    if isBundle env c then
      let fs := fieldNames env c
      let un := (List.range fs.size).filter (fun j => !used.contains (.field c j)) |>.map (fs[·]!)
      if !un.isEmpty then
        let mi := (env.getModuleIdxFor? c).map (fun i => toString env.header.modules[i.toNat]!.module)
        all := all.push s!"{mi.getD "?"} {c} ({fs.size} fields): {un}"
  IO.FS.writeFile "scratch/pi0-fold/unused-all.txt" ("\n".intercalate (all.qsort (· < ·)).toList ++ "\n")
  logInfo m!"PRUNE bundles with unused fields: {all.size}"
  -- the prune set: everything the unused top fields feed (all of it is unused too)
  let mut fwd : Std.HashMap Node (Array Node) := {}
  for (dst, srcs) in st.edges.toList do
    for src in srcs do fwd := fwd.insert src ((fwd.getD src #[]).push dst)
  let mut reach : Std.HashSet Node := {}
  let mut q : Array Node := #[]
  for s in tops do
    let fs := fieldNames env s
    for j in [:fs.size] do
      if !used.contains (.field s j) then
        reach := reach.insert (.field s j)
        q := q.push (.field s j)
  while !q.isEmpty do
    let n := q.back!
    q := q.pop
    for d in fwd.getD n #[] do
      if !reach.contains d then
        reach := reach.insert d
        q := q.push d
  let mut ps : Array String := #[]
  for n in reach.toList do
    match n with
    | .field s j =>
      let mi := (env.getModuleIdxFor? s).map (fun i => toString env.header.modules[i.toNat]!.module)
      ps := ps.push s!"FIELD {mi.getD "?"} {s}.{(fieldNames env s)[j]!}"
    | .const c =>
      if isOneProofModule env c then
        let mi := (env.getModuleIdxFor? c).map (fun i => toString env.header.modules[i.toNat]!.module)
        ps := ps.push s!"CONST {mi.getD "?"} {c}{if used.contains n then " (USED!)" else ""}"
  IO.FS.writeFile "scratch/pi0-fold/prune-set.txt" ("\n".intercalate (ps.qsort (· < ·)).toList ++ "\n")
  logInfo m!"PRUNE prune set: {ps.size} entries"
