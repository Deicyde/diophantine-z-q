import ZInQKernel.OneProof.Main
import Lean
/-! h21-combine (from fold-kleiman2's ClosureCheck): the closure (types and values) of `ZInQ.OneProof.frozenTarget`
and its top-level binders. After the fold, `H21CSteps.TYZThm21Span` (h21S) stays in the closure as a proved
intermediate statement (`H21Combine.tyzThm21Span_of_GP`), so the check is that no binder of `frozenTarget` has it
(or `TYZThm21PairsC`, `TYZThm21SpanG`, `TYZThm21SpanPrinted`) as type; `TYZThm21SpanGP` must be a binder;
`sorryAx` must be absent. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

run_cmd do
  let env ← getEnv
  let names : List Name := [
    `ZInQ.Contrib.H21CSteps.TYZThm21Span, `ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC,
    `ZInQ.Contrib.H21GChar.TYZThm21SpanG, `ZInQ.Contrib.H21Lcal.TYZThm21SpanPrinted,
    `ZInQ.Contrib.H21Combine.TYZThm21SpanGP, `ZInQ.Contrib.H21Combine.tyzThm21PairsC_of_GP,
    `ZInQ.Contrib.H21GChar.tyzChiCl_eq_gchar, `ZInQ.Contrib.H21Lcal.lcalSqPrinted_eq, `sorryAx]
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
  IO.println s!"frozenTarget: closure {seen.size}"
  for b in names do
    IO.println s!"  contains {b}: {seen.contains b}"
  if let some ci := env.find? `ZInQ.OneProof.frozenTarget then
    let rec binders : Expr → List (Name × Expr)
      | .forallE n t b _ => (n, t) :: binders b
      | _ => []
    for (n, t) in binders ci.type do
      let hit := t.getUsedConstants.toList.filter (names.contains ·)
      IO.println s!"  binder {n} : {t.getAppFn.constName?.getD `_}{if hit.isEmpty then "" else s!"  CHECKED {hit}"}"
