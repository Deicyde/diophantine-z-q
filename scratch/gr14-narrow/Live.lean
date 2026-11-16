import ZInQKernel.OneProof.Main
import Lean
/-! gr14-narrow probe: every constant in the closure of `ZInQ.OneProof.frozenTarget` whose type mentions
R19 / GaudronRemondThm14 (level T), and every closure constant whose value mentions a level-T constant or
the reverse-isogeny theorems. -/
open Lean

def g14Closure (env : Environment) (root : Name) : NameSet := Id.run do
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

def g14Suffixes : List String := ["R19_GaudronRemond", "GaudronRemondThm14", "isogenyReverseExists_of_r19",
  "reverseIsogeny_of_leaves3", "reverseIsogeny_of_leaves", "MilneIsogenyQuasiInverse", "IsogenyReverseExists"]

def g14Watched (n : Name) : Bool := match n with
  | .str _ s => g14Suffixes.contains s
  | _ => false

run_cmd do
  let env ← getEnv
  let s := g14Closure env `ZInQ.OneProof.frozenTarget
  logInfo m!"closure size {s.size}"
  let mut T : NameSet := {}
  let mut lines : Array String := #[]
  for n in s.toList do
    if g14Watched n then lines := lines.push s!"WATCHED-LIVE {n}"
  for n in s.toList do
    if let some ci := env.find? n then
      let tc := ci.type.getUsedConstants
      if tc.any g14Watched then
        T := T.insert n
        lines := lines.push s!"TYPE {n} : mentions {(tc.filter g14Watched).toList}"
  for n in s.toList do
    if let some ci := env.find? n then
      if let some v := ci.value? (allowOpaque := true) then
        let vc := v.getUsedConstants
        let hits := vc.filter fun c => g14Watched c || (T.contains c && c != n)
        if hits.size > 0 then
          lines := lines.push s!"VALUE {n} uses {hits.toList.eraseDups}"
  logInfo m!"{String.intercalate "\n" lines.toList}"
