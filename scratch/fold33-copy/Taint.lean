import ZInQKernel.OneProof.H.TailZ48
import Lean
/-! fold33-copy: the declarations a copy reroute must copy.

Carriers: the structures in the closure of `HDec.HSyn.sixContactMin_of_open41` (TailZ48, the top before the folds)
named `OpenResearchLeaves<k>`, k ≥ 14, that have a field named `sga3_VIB_3_10` or `sga3_VIB_3_10_Nbhd` (sga3-nbhd) or `mumfordGroupLaw` or
`mumfordGroupLawConn` (goodmodel-iso). Tainted: every constant of the closure whose type or value mentions a carrier or
a tainted constant, transitively. Each line: `T <module> <name> <kind>`, kind `src` (a source declaration, to be
copied) or `aux` (projection, constructor, recursor, matcher, internal: regenerated with its declaration). -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def fieldNames : List String := ["sga3_VIB_3_10", "sga3_VIB_3_10_Nbhd", "mumfordGroupLaw", "mumfordGroupLawConn"]

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut uses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[`HDec.HSyn.sixContactMin_of_open41]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let mut us := ci.type.getUsedConstants
      if let some v := ccValue? ci then
        us := us ++ v.getUsedConstants
      -- a structure depends on its fields' types through its constructor
      if let .inductInfo iv := ci then
        for ctor in iv.ctors do us := us.push ctor
      uses := uses.insert c us
      todo := todo ++ us
  IO.println s!"closure size {seen.size}"
  let mut carriers : NameSet := {}
  for c in seen.toList do
    if isStructure env c then
      let fs := getStructureFields env c
      let gen := (c.toString.drop "HDec.HSyn.OpenResearchLeaves".length).toString.toNat?
      if fs.any (fun f => fieldNames.contains f.toString) then
        if c.toString.startsWith "HDec.HSyn.OpenResearchLeaves" && gen.getD 0 ≥ 14 then
          carriers := carriers.insert c
        else
          IO.println s!"not a carrier (older generation): {c}" 
  IO.println s!"carriers {carriers.toList.map toString |>.toArray.qsort (· < ·)}"
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (c, us) in uses.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  let mut tainted : NameSet := {}
  let mut q : Array Name := #[]
  for c in carriers.toList do
    tainted := tainted.insert c
    q := q.push c
  while !q.isEmpty do
    let c := q.back!
    q := q.pop
    for d in rev.getD c #[] do
      if !tainted.contains d then
        tainted := tainted.insert d
        q := q.push d
  let mut out : Array String := #[]
  for c in tainted.toList do
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    let isAux := (env.getProjectionFnInfo? c).isSome || isAuxRecursor env c || isNoConfusion env c ||
      c.isInternal || (Lean.Meta.isMatcherCore env c) ||
      (match env.find? c with | some (.ctorInfo _) => true | some (.recInfo _) => true | _ => false) ||
      (match c with | .str p _ => carriers.contains p && !(env.find? c |>.map (·.isTheorem) |>.getD false) | _ => false)
    out := out.push s!"T {mod} {c} {if isAux then "aux" else "src"}"
  IO.println s!"tainted {tainted.size}"
  for s in out.qsort (· < ·) do IO.println s
