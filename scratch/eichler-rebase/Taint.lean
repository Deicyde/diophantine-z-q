import ZInQKernel.OneProof.H.TailZ55
import Lean
/-! eichler-rebase: what the bypass of `gonzalezRotgerProp56X6` must copy on main's top
`HDec.HSyn.sixContactMin_of_open48` (TailZ55).

Part 1 (field taint, as fold33-pic's FieldTaint.lean): forward taint from the bundle field
`gonzalezRotgerProp56X6`. A bundle map (`fun .. => S.mk a₁ … aₙ`) taints the fields `aᵢ` that read a tainted
projection; every other constant reading one is a terminal consumer (`TERM`).
Part 2 (copy set, as fold33-pic's Taint2.lean): `T` = constants whose value depends on a projection of a
tainted field; `S` = constants (not `T`) whose type mentions a structure carrying a tainted field. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

partial def stripLam : Expr → Expr
  | .lam _ _ b _ => stripLam b
  | .letE _ _ _ b _ => stripLam b
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
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open48]
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
  -- part 1
  let mut fields : Std.HashSet String := {}
  fields := fields.insert "gonzalezRotgerProp56X6"
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
  -- part 2
  let isSeed : Name → Bool := fun n =>
    match projField env n with | some s => fields.contains s | none => false
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (c, us) in valUses.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  let mut tainted : NameSet := {}
  let mut q : Array Name := #[]
  for c in seen.toList do
    if isSeed c then
      tainted := tainted.insert c
      q := q.push c
  while !q.isEmpty do
    let c := q.back!
    q := q.pop
    for d in rev.getD c #[] do
      if !tainted.contains d then
        tainted := tainted.insert d
        q := q.push d
  let mut carriers : NameSet := {}
  for c in seen.toList do
    if isStructure env c then
      if (getStructureFields env c).any (fun f => fields.contains f.toString) then
        carriers := carriers.insert c
  IO.println s!"carriers {(carriers.toList.map toString).toArray.qsort (· < ·)}"
  for c in carriers.toList do
    let fs := (getStructureFields env c).filter (fun f => fields.contains f.toString)
    if fs.size != 1 then IO.println s!"MULTI {c} {fs}"
  let mut out : Array String := #[]
  for c in tainted.toList do
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    out := out.push s!"T {mod} {c}"
  for c in seen.toList do
    if tainted.contains c then continue
    if let some ci := env.find? c then
      if ci.type.getUsedConstants.any (carriers.contains ·) then
        let mod := match env.getModuleIdxFor? c with
          | some i => toString (env.header.moduleNames[i.toNat]!)
          | none => "?"
        out := out.push s!"S {mod} {c}"
  IO.println s!"tainted {tainted.size}"
  for s in out.qsort (· < ·) do IO.println s
