import ZInQKernel.OneProof.Main
import Lean
/-! sga735-finish: the copy set for re-typing r6 (`RaynaudCriterionNF` ↦ nilpotent form) and the field.
Candidates: (A) constants whose value depends on a projection `sga7_IX_3_5_ForwardGeom` / `semistableUnipotent`;
(B) constants whose type mentions `RaynaudCriterionNF` or a structure carrying a field of type A or B (iterated).
Copy: the least set containing the top theorem and closed under "a dependency that is a candidate". -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def isSeed (env : Environment) (n : Name) : Bool :=
  match n with
  | .str _ s => (s == "sga7_IX_3_5_ForwardGeom" || s == "semistableUnipotent") && (env.getProjectionFnInfo? n).isSome
  | _ => false

run_cmd do
  let env ← getEnv
  let top := `HDec.HSyn.sixContactMin_of_open48
  let mut seen : NameSet := {}
  let mut valUses : Std.HashMap Name (Array Name) := {}
  let mut allUses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[top]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let tu := ci.type.getUsedConstants
      let mut us := tu
      if let some v := ccValue? ci then
        let vu := v.getUsedConstants
        valUses := valUses.insert c vu
        us := us ++ vu
      allUses := allUses.insert c us
      todo := todo ++ us
  IO.println s!"closure size {seen.size}"
  -- (A) value taint
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (c, us) in valUses.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  let mut tA : NameSet := {}
  let mut q : Array Name := #[]
  for c in seen.toList do
    if isSeed env c then
      tA := tA.insert c; q := q.push c
  while !q.isEmpty do
    let c := q.back!
    q := q.pop
    for d in rev.getD c #[] do
      if !tA.contains d then
        tA := tA.insert d; q := q.push d
  -- (B) type mentions, iterated through carriers
  let mut bad : NameSet := ({} : NameSet).insert `HDec.PkgI2.RaynaudCriterionNF |>.insert `GapNeron.RaynaudCriterionNF
  -- carriers of A seeds
  for c in tA.toList do
    if isSeed env c then
      if let some info := env.getProjectionFnInfo? c then
        if let some (.ctorInfo cv) := env.find? info.ctorName then bad := bad.insert cv.induct
  let mut changed := true
  let mut tB : NameSet := {}
  while changed do
    changed := false
    for c in seen.toList do
      if tB.contains c || bad.contains c then continue
      if let some ci := env.find? c then
        if ci.type.getUsedConstants.any (bad.contains ·) then
          tB := tB.insert c
          -- a structure whose field type mentions bad: its constructor type mentions bad
          if let .ctorInfo cv := ci then
            if !bad.contains cv.induct then
              bad := bad.insert cv.induct; changed := true
  let cand : Name → Bool := fun c => tA.contains c || tB.contains c || bad.contains c
  -- copy set
  let mut copy : NameSet := {}
  let mut q2 : Array Name := #[top]
  while !q2.isEmpty do
    let c := q2.back!
    q2 := q2.pop
    if copy.contains c then continue
    copy := copy.insert c
    for d in allUses.getD c #[] do
      if cand d && !copy.contains d then q2 := q2.push d
  IO.println s!"tA {tA.size} tB {tB.size} bad {bad.size} copy {copy.size}"
  IO.println s!"bad structures {bad.toList}"
  let mut out : Array String := #[]
  for c in copy.toList do
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    let k := if tA.contains c then "A" else if bad.contains c then "S" else "B"
    out := out.push s!"{k} {mod} {c}"
  for s in out.qsort (· < ·) do IO.println s
