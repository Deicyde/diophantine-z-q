import ZInQKernel.OneProof.Main
import Lean
/-! piczero-char0: field-level forward taint from bundle field `picZeroAbVar` through `frozenTarget`'s closure.
A constant whose value is `fun .. => S.mk a₁ … aₙ` (a bundle map) taints only the fields `aᵢ` that use a tainted
projection (and those field names become seeds); any other constant using a tainted projection or a tainted
constant is reported as a terminal consumer. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

partial def stripLam : Expr → Expr
  | .lam _ _ b _ => stripLam b
  | .mdata _ b => stripLam b
  | e => e

def projField (env : Environment) (n : Name) : Option String :=
  match env.getProjectionFnInfo? n, n with
  | some _, .str _ s => some s
  | _, _ => none

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut valUses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then
        let us := v.getUsedConstants
        valUses := valUses.insert c us
        todo := todo ++ us
  let consts := valUses.toArray
  IO.println s!"closure size {seen.size}"
  let mut fields : Std.HashSet String := {}
  fields := fields.insert "picZeroAbVar"
  let mut taintedC : NameSet := {}
  let mut changed := true
  let mut iter := 0
  let mut lines : Array String := #[]
  while changed do
    changed := false
    iter := iter + 1
    lines := #[]
    for (c, us) in consts do
      let bad : Name → Bool := fun u =>
        (match projField env u with | some s => fields.contains s | none => false) || taintedC.contains u
      if !(us.any bad) then continue
      if (projField env c).isSome then continue
      let some ci := env.find? c | continue
      let some v := ccValue? ci | continue
      let body := stripLam v
      let fn := body.getAppFn
      let mut isMap := false
      if let .const ctor _ := fn then
        if let some (.ctorInfo cv) := env.find? ctor then
          if isStructure env cv.induct then
            isMap := true
            let fs := getStructureFields env cv.induct
            let args := body.getAppArgs
            for i in [0:fs.size] do
              let a := args[cv.numParams + i]!
              let ua := a.getUsedConstants
              let hits := ua.filter bad
              if hits.isEmpty then continue
              let fname := fs[i]!.toString
              let forward := hits.all (fun u => projField env u == some fname)
              if !forward then
                lines := lines.push s!"EDGE {c} : field {fname} <- {hits.toList}"
              if !fields.contains fname then
                fields := fields.insert fname
                changed := true
      if !isMap then
        lines := lines.push s!"TERM {c} USES {(us.filter bad).toList}"
        if !taintedC.contains c then
          taintedC := taintedC.insert c
          changed := true
  IO.println s!"iterations {iter}; tainted fields {fields.toList}"
  for s in lines.qsort (· < ·) do IO.println s
