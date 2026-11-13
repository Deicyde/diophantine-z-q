import Mathlib
section LeafFoldCheckSec

open Lean Elab Command Meta

/-- `t` is a proposition (failures count as no). -/
def LeafFoldCheck.isProofType (t : Expr) : MetaM Bool := do
  try Meta.isProp t catch _ => pure false

/-- Normal form for `#hdec_same`: every constant whose type is a proposition (a theorem, an
auxiliary `_proof_n`, a `Fact` instance, …) is replaced by `proofOf T` with `T` its normalized
type (proof irrelevance: two proofs of one proposition are interchangeable, and their
auto-generated names differ between files); every other constant `c` is renamed to `stripN c`. -/
partial def LeafFoldCheck.norm (stripN : Name → Name) (fuel : Nat) (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let mut m : Std.HashMap Name Expr := {}
  for c in e.getUsedConstants do
    if let some ci := env.find? c then
      let isPf ← LeafFoldCheck.isProofType ci.type
      if isPf then
        let t ← if fuel = 0 then pure (mkConst `LeafFoldCheck.deep)
          else LeafFoldCheck.norm stripN (fuel - 1) ci.type
        m := m.insert c (mkApp (mkConst `LeafFoldCheck.proofOf) t)
  return e.replace fun
    | .const c us => some ((m.get? c).getD (.const (stripN c) us))
    | _ => none

/-- The comparison behind `#hdec_same`: `n` (an `HDec.` name) against `top`; a nested `HDec.Z`
against `P.Z` if that exists, else against `Z`. -/
def LeafFoldCheck.run (n top P : Name) : TermElabM Unit := do
  let env ← getEnv
  let strip : Name → Name := fun c =>
    if c == n then top
    else if (`HDec).isPrefixOf c then
      let z := c.replacePrefix `HDec .anonymous
      if !P.isAnonymous && env.contains (P ++ z) then P ++ z else z
    else c
  let mut todo : Array Name := #[n]
  let mut seen : NameSet := {}
  let mut bad : Array String := #[]
  let mut count : Nat := 0
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | bad := bad.push s!"{c}: not found"
    -- proofs are compared through their types only (where they occur)
    if (← LeafFoldCheck.isProofType ci.type) && c != n then continue
    count := count + 1
    let some ri := env.find? (strip c) | bad := bad.push s!"{c}: no root counterpart"
    if (← LeafFoldCheck.norm strip 8 ci.type) != (← LeafFoldCheck.norm id 8 ri.type) then
      bad := bad.push s!"{c}: types differ"
    let isThm := match ci with | .thmInfo _ => true | _ => false
    let mut used := ci.type.getUsedConstants
    if !isThm then
      match ci.value?, ri.value? with
      | some v, some w =>
        if (← LeafFoldCheck.norm strip 8 v) != (← LeafFoldCheck.norm id 8 w) then
          bad := bad.push s!"{c}: bodies differ"
        used := used ++ v.getUsedConstants
      | none, none => pure ()
      | _, _ => bad := bad.push s!"{c}: kinds differ"
    match ci with
    | .inductInfo v => used := used ++ v.ctors.toArray
    | _ => pure ()
    for u in used do
      if (`HDec).isPrefixOf u && !seen.contains u then todo := todo.push u
  if bad.isEmpty then
    logInfo m!"{n}: {count} HDec constants compared; each is its root counterpart verbatim \
      (up to the prefix and the names of proofs)"
  else
    logInfo m!"{n}: {count} HDec constants compared; differences:\n\
      {String.intercalate "\n" bad.toList}"

/-- `#hdec_same HDec.X`: compare `HDec.X` with the root `X`, recursively through every `HDec.`
constant that the types and (for definitions) the bodies mention: the types and bodies must agree
after deleting the prefix `HDec.`, up to the names of proofs (`LeafFoldCheck.norm`). Reports the
number of constants compared and every difference. -/
elab "#hdec_same " a:ident : command => liftTermElabM do
  LeafFoldCheck.run a.getId (a.getId.replacePrefix `HDec .anonymous) .anonymous

/-- `#hdec_same_as HDec.X Y P`: compare `HDec.X` with `Y`, and a nested `HDec.Z` with `P.Z` if that
exists, else with `Z` (for a Contrib file that restates `X` and some of the definitions it uses
inside a namespace `P`). -/
elab "#hdec_same_as " a:ident b:ident c:ident : command => liftTermElabM do
  LeafFoldCheck.run a.getId b.getId c.getId

end LeafFoldCheckSec
theorem aux1 : (2 : ℕ) ≠ 0 := by decide
def foo : Fin 3 := ⟨1, by decide⟩
def bar : Prop := ∀ x : Fin 3, x = foo ∨ x ≠ foo
namespace HDec
theorem aux2 : (5 : ℕ) ≠ 0 := by decide
def foo : Fin 3 := ⟨1, by omega⟩
def bar : Prop := ∀ x : Fin 3, x = foo ∨ x ≠ foo
def baz : Prop := ∀ x : Fin 3, x = foo
end HDec
def baz : Prop := ∀ x : Fin 3, x ≠ foo
#hdec_same HDec.bar
#hdec_same HDec.baz
namespace Q.R
def foo2 : Fin 3 := ⟨1, by decide⟩
def bar2 : Prop := ∀ x : Fin 3, x = foo2 ∨ x ≠ foo2
end Q.R
namespace HDec
def foo2 : Fin 3 := ⟨1, by decide⟩
def bar3 : Prop := ∀ x : Fin 3, x = foo2 ∨ x ≠ foo2
end HDec
#hdec_same_as HDec.bar3 Q.R.bar2 Q.R
