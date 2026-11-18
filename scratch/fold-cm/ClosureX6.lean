import ZInQKernel.OneProof.Main
/-! fold-cm: the integrator's closure scan after both components. In the closure of `ZInQ.OneProof.frozenTarget`, list the
constants whose name mentions González–Rotger, `X6`/`x6` (the `_y3x6` copy suffix excluded), R5pt or FS5/NoCM, each with
its type head when it is a structure projection, and one referrer in the closure. -/
open Lean in
def fcValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

open Lean Meta in
run_meta do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  let mut refBy : Std.HashMap Name Name := {}
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let us := ci.type.getUsedConstants ++ ((fcValue? ci).map (·.getUsedConstants) |>.getD #[])
      for u in us do
        if !refBy.contains u then refBy := refBy.insert u c
        todo := todo.push u
  let has (x y : String) : Bool := (x.splitOn y).length > 1
  let strip (x : String) : String := (x.replace "_y3x6" "").replace "y3x6" ""
  let mut n := 0
  for c in seen.toList do
    let x := strip c.toString
    if has x "GonzalezRotger" || has x "gonzalezRotger" || has x "X6" || has x "x6" || has x "R5pt" || has x "FS5" || has x "NoCM" then
      n := n + 1
      let ty ← match env.find? c with
        | some ci => do
            let t := ci.type
            let hd := (t.getForallBody.getAppFn.constName?).getD `_
            pure s!"{hd}"
        | none => pure "?"
      IO.println s!"{c}\ttype-head {ty}\treferrer {refBy.getD c `_}"
  IO.println s!"closure {seen.size}; matching {n}"
