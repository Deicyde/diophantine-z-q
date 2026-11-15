import ZInQKernel.OneProof.Main
import Lean
/-! triage2: is the clause `LeafAdopt.R1pi0Props X` (and `GeometricallyConnected`) ever *used* on the live path?
For every constant in the closure of `ZInQ.OneProof.frozenTarget`, walk its value; at every lambda / let /
forall binder whose type mentions the watched constants, report whether the bound variable occurs in the body.
A discarded `-` pattern gives an unused binder; a real consumer or a producer gives a used one. -/
open Lean

def p0Closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then todo := todo ++ v.getUsedConstants
  return seen

def p0Watched : List Name := [`LeafQM.AV.R1heckeProps, `LeafQM.AV.X6Surj, `LeafQM.AV.R5ptProps, `LeafQM.AV.R1recProps, `LeafQM.AV.CMExists, `HDec.LeafAdopt.R2X6PropsIff, `LeafQM.AV.R2X6Props]

def p0Mentions (e : Expr) : Bool := (e.find? fun x => match x with
  | .const n _ => p0Watched.contains n
  | _ => false).isSome

/-- binder type is exactly the watched clause (head constant), not a conjunction containing it. -/
def p0Head (e : Expr) : Bool := match e.consumeMData.getAppFn with
  | .const n _ => p0Watched.contains n
  | _ => false

partial def p0WalkOld (e : Expr) (acc : Array (String × Bool)) : Array (String × Bool) :=
  match e with
  | .lam n t b _ | .forallE n t b _ =>
      let acc := if p0Head t then acc.push (toString n, b.hasLooseBVar 0) else acc
      p0Walk b (p0Walk t acc)
  | .letE n t v b _ =>
      let acc := if p0Head t then acc.push (toString n, b.hasLooseBVar 0) else acc
      p0Walk b (p0Walk v (p0Walk t acc))
  | .app f a => p0Walk a (p0Walk f acc)
  | .mdata _ b => p0Walk b acc
  | .proj _ _ b => p0Walk b acc
  | _ => acc

def p0HeadIs (w : Name) (e : Expr) : Bool := e.consumeMData.getAppFn.isConstOf w

partial def p0WalkW (w : Name) (e : Expr) (acc : Array (String × Bool)) : Array (String × Bool) :=
  match e with
  | .lam n t b _ | .forallE n t b _ =>
      let acc := if p0HeadIs w t then acc.push (toString n, b.hasLooseBVar 0) else acc
      p0WalkW w b (p0WalkW w t acc)
  | .letE n t v b _ =>
      let acc := if p0HeadIs w t then acc.push (toString n, b.hasLooseBVar 0) else acc
      p0WalkW w b (p0WalkW w v (p0WalkW w t acc))
  | .app f a => p0WalkW w a (p0WalkW w f acc)
  | .mdata _ b => p0WalkW w b acc
  | .proj _ _ b => p0WalkW w b acc
  | _ => acc

run_cmd do
  let env ← getEnv
  let s := p0Closure env `ZInQ.OneProof.frozenTarget
  logInfo m!"closure size {s.size}"
  let mut lines : Array String := #[]
  for n in s.toList do
    if let some ci := env.find? n then
      if let some v := ci.value? (allowOpaque := true) then
        if !p0Mentions v then continue
        for w in p0Watched do
          let r := p0WalkW w v #[]
          if r.size == 0 then continue
          let used := r.filter (·.2)
          lines := lines.push s!"{w} | {n}: binders {r.size}, used {used.size}"
  logInfo m!"{String.intercalate "\n" lines.toList}"
