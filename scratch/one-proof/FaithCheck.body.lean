
/-! op-dedupe faithfulness check (run with the original H chain on LEAN_PATH, see log-dedupe.md).

For every mapped name `n` (H copy `HDec.n`, kernel `n`), the copy is *faithful* when its type (and value, for
definitions; constructor types, for inductives) equals the kernel's after renaming every faithful `HDec.m` to `m`.
Greatest fixpoint, starting from all mapped names. Writes `/tmp/opd_faith.tsv`: name, status, reason. -/

open Lean Meta Elab Command

namespace OpDedupe

def hdec : Name := `HDec

/-- strip the leading `HDec` component -/
def stripH : Name → Option Name
  | n => 
    let cs := n.components
    match cs with
    | c :: rest => if c == hdec then some (rest.foldl (fun a b => a ++ b) Name.anonymous) else none
    | [] => none

/-- longest prefix of `x` that is in `S` -/
def owner (S : NameSet) : Name → Option Name
  | .anonymous => none
  | x@(.str p _) => if S.contains x then some x else owner S p
  | x@(.num p _) => if S.contains x then some x else owner S p

structure Ctx where
  env : Environment
  mapped : NameSet
  hnames : NameSet
  privK : Std.HashMap Name Name   -- user name -> kernel private name

def ren (c : Ctx) (F : NameSet) (n : Name) : Option Name :=
  let (isPriv, u) := match privateToUserName? n with
    | some u => (true, u) | none => (false, n)
  match stripH u with
  | none => none
  | some x =>
    let ok : Bool := match owner c.mapped x with
      | some o => F.contains o
      | none => !(c.hnames.contains x)
    if !ok then none else
    if isPriv then c.privK.get? x
    else if c.env.contains x then some x else none

/-- Identifications made by hand: def-faltings' structure copy `ZInQ.DefFaltings.AbVar` (no universe) is the
kernel's alias of `PkgI3.AbVar.{0}`; its fields and `baseChange`, `dim`, `ZInQ.H5Neron.AbVar.zero` are PkgI3's. -/
def manual : List (Name × Name × List Level) :=
  [(`HDec.ZInQ.DefFaltings.AbVar, `ZInQ.DefFaltings.AbVar, [])] ++
  ([`X, `grp, `proper, `smooth, `geomInt, `mk, `baseChange, `dim].map fun f =>
    (`HDec.ZInQ.DefFaltings.AbVar ++ f, `PkgI3.AbVar ++ f, [Level.zero])) ++
  [(`HDec.ZInQ.H5Neron.AbVar.zero, `PkgI3.AbVar.zero, [])]

partial def renExpr (c : Ctx) (F : NameSet) (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      match manual.find? (·.1 == n) with
      | some (_, n', _) =>
        let k := match c.env.find? n' with | some ci => ci.levelParams.length | none => 0
        some (.const n' ((List.replicate (k - us.length) Level.zero) ++ us))
      | none => (ren c F n).map (fun n' => .const n' us)
    | .proj s i b =>
      let s' := match manual.find? (·.1 == s) with
        | some (_, n', _) => if n' == `ZInQ.DefFaltings.AbVar then `PkgI3.AbVar else n'
        | none => (ren c F s).getD s
      if s' == s then none else some (.proj s' i (renExpr c F b))
    | _ => none

def deq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  try
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 400000 * 1000 }) do
      withCurrHeartbeats <| withoutModifyingState <| isDefEq a b
  catch _ => return false

def diffC (a b : Expr) : String :=
  let x := a.getUsedConstants; let y := b.getUsedConstants
  s!"H-only {(x.filter (!y.contains ·)).toList.take 4} K-only {(y.filter (!x.contains ·)).toList.take 4}"

def cmp (c : Ctx) (F : NameSet) (n : Name) : MetaM (Option String) := do
  let some hc := c.env.find? (hdec ++ n) | return some "no HDec constant"
  let some kc := c.env.find? n | return some "no kernel constant"
  if hc.levelParams != kc.levelParams then return some "level params"
  let ht := renExpr c F hc.type
  if !(← deq ht kc.type) then return some s!"type {diffC ht kc.type}"
  match hc, kc with
  | .defnInfo h, .defnInfo k =>
    let hv := renExpr c F h.value
    if !(← deq hv k.value) then return some s!"value {diffC hv k.value}"
  | .opaqueInfo h, .opaqueInfo k =>
    if !(← deq (renExpr c F h.value) k.value) then return some "value"
  | .thmInfo _, .thmInfo _ => pure ()
  | .inductInfo h, .inductInfo k =>
    if h.ctors.length != k.ctors.length || h.numParams != k.numParams || h.numIndices != k.numIndices then
      return some "inductive shape"
    for hn in h.ctors, kn in k.ctors do
      let some hcc := c.env.find? hn | return some "ctor"
      let some kcc := c.env.find? kn | return some "ctor"
      if !(← deq (renExpr c F hcc.type) kcc.type) then return some s!"ctor type {kn}"
  | .axiomInfo _, .axiomInfo _ => pure ()
  | _, _ => return some "kind"
  return none

elab "#op_dedupe_check" : command => do
  let env ← getEnv
  let mapped := (← IO.FS.lines "/tmp/opd_mapped.txt").filter (· ≠ "") |>.map String.toName
  let hnames := (← IO.FS.lines "/tmp/opd_hnames.txt").filter (· ≠ "") |>.map String.toName
  let mut privK : Std.HashMap Name Name := {}
  for (n, _) in env.constants.toList do
    if let some u := privateToUserName? n then
      if (stripH u).isNone then privK := privK.insert u n
  let c : Ctx := { env, mapped := mapped.foldl (·.insert ·) {}, hnames := hnames.foldl (·.insert ·) {}, privK }
  let mut F : NameSet := c.mapped
  let mut why : Std.HashMap Name String := {}
  let mut rnd : Nat := 0
  repeat
    rnd := rnd + 1
    let mut bad : Array Name := #[]
    for n in mapped do
      if F.contains n then
        if let some r ← liftTermElabM (cmp c F n) then
          bad := bad.push n; why := why.insert n s!"{r} (rnd {rnd})"
    logInfo m!"rnd {rnd}: {bad.size} removed"
    if bad.isEmpty then break
    F := bad.foldl (·.erase ·) F
  let lines := mapped.map fun n =>
    s!"{n}\t{if F.contains n then "FAITHFUL" else "DIVERGENT"}\t{why.getD n ""}"
  IO.FS.writeFile "/tmp/opd_faith.tsv" (String.intercalate "\n" lines.toList ++ "\n")
  logInfo m!"faithful: {mapped.filter F.contains |>.size} of {mapped.size}"

end OpDedupe

#op_dedupe_check
