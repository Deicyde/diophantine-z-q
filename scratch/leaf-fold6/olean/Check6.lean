import TailO
open Lean
-- leaf-fold6: the conclusion is the kernel's own `ZInQ.SixContactMin`; the dependency closure of
-- `sixContactMin_of_open6`; the head constant of every bundle field's type; every field type is, as a term,
-- the type of the same field in its source bundle (leaf-fold5's `OpenTextbookLeaves5`, `OpenAddedLeaves5`,
-- `OpenGlue5`, or leafq-check's `OpenAddedLeaves10`, here `OpenAddedLeavesQ10`), or for `t8` the kernel's Prop.
example : (∀ (_ : HDec.HSyn.OpenResearchLeaves5) (_ : HDec.HSyn.OpenTextbookLeaves6)
    (_ : HDec.HSyn.OpenAddedLeaves6) (_ : HDec.HSyn.OpenGlue6), _root_.ZInQ.SixContactMin) :=
  HDec.HSyn.sixContactMin_of_open6
#print axioms HDec.HSyn.sixContactMin_of_open6
#print axioms HDec.HSyn.sixContactMin_of_open6_poincare

def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      visited := visited.insert n
      if let some ci := env.find? n then
        for m in ci.getUsedConstantsAsSet.toList do
          if !visited.contains m then stack := m :: stack
  return visited

#eval show CoreM Unit from do
  let env ← getEnv
  for root in [`HDec.HSyn.sixContactMin_of_open6, `HDec.HSyn.sixContactMin_of_open6_poincare] do
    let visited := closureOf env root
    IO.println s!"== {root}: closure size {visited.size}"
    for n in [`sorryAx,
        `HDec.LeafQCheck.gammaStarGen_proof, `HDec.LeafQCheck.VB.valenceBound_of_formula,
        `HDec.LeafQCheck.VB.ellipticOrderLe6_proof,
        `HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of,
        `HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5,
        `HDec.LeafQCheck.HM.base2_of_base3, `HDec.LeafQCheck.HM.qmHauptmodul_of_base2,
        `HDec.LeafQCheck.HM.orbit4, `HDec.LeafQCheck.HM.orbit3, `HDec.LeafQCheck.HM.orbit24,
        `HDec.HSyn.G0Split.FibreQM.PeriodGlue.LQ20.s20WeightExact_of,
        `HDec.HSyn.t8_ofK6, `ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage,
        `HDec.HSyn.t8_of_simpleImage5, `HDec.AVB2.t11b_of_exists, `HDec.HSyn.torsionStructure_ofK5,
        `HDec.HSyn.heckeVertWitness_of_leaves5, `HDec.ModelGlue.heckeVertWitness_of_curveBijIso,
        `ZInQ.SmoothFibre.smoothFibreReduced, `ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed,
        `ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split, `ZInQ.Contrib.NeronC.neronModelExists_of_extension,
        `HDec.HSyn.sixContactMin_of_open4, `HDec.HSyn.sixContactMin_of_open5,
        `HDec.HSyn.sixContactMin_of_openQ10] do
      IO.println s!"  {n}: {visited.contains n}"

/-- the type of field `f` of the Prop structure `s` (the projection's type with the structure argument
instantiated; fields of a Prop structure of Props do not depend on it). -/
def fieldType (s f : Name) : MetaM Expr := do
  let some pf := (← getEnv).find? (s ++ f) | throwError "no field {s ++ f}"
  let b := pf.type.bindingBody!
  if b.hasLooseBVars then throwError "field {s ++ f} depends on the structure"
  pure b

#eval show MetaM Unit from do
  let env ← getEnv
  let mut nK := 0
  let mut nAll := 0
  for s in [`HDec.HSyn.OpenResearchLeaves5, `HDec.HSyn.OpenTextbookLeaves6, `HDec.HSyn.OpenAddedLeaves6,
      `HDec.HSyn.OpenGlue6] do
    let some info := getStructureInfo? env s | IO.println s!"no {s}"
    IO.println s!"== {s}: {info.fieldNames.size} fields"
    for f in info.fieldNames do
      let ty ← fieldType s f
      let ty' ← Meta.forallTelescope ty fun _ b => pure b
      let hd := ty'.getAppFn.constName?
      let kern := match hd with
        | some n => !(`HDec).isPrefixOf n
        | none => false
      nAll := nAll + 1
      if kern then nK := nK + 1
      IO.println s!"  {f} : {hd}{if kern then "  [kernel]" else ""}"
  IO.println s!"fields {nAll}, on kernel constants {nK}"

-- every field type equals (as an `Expr`, `==`) the type of the same field in its source bundle
#eval show MetaM Unit from do
  let env ← getEnv
  let mut ok := true
  let src : List (Name × List Name) :=
    [(`HDec.HSyn.OpenTextbookLeaves6, [`HDec.HSyn.OpenTextbookLeaves5]),
     (`HDec.HSyn.OpenAddedLeaves6, [`HDec.HSyn.OpenAddedLeaves5, `HDec.HSyn.OpenAddedLeavesQ10]),
     (`HDec.HSyn.OpenGlue6, [`HDec.HSyn.OpenGlue5])]
  for (s, srcs) in src do
    let some info := getStructureInfo? env s | IO.println s!"no {s}"
    for f in info.fieldNames do
      let ty ← fieldType s f
      let mut found : Option Name := none
      for s' in srcs do
        if found.isNone && (env.find? (s' ++ f)).isSome then
          let ty2 ← fieldType s' f
          if ty == ty2 then found := some s'
      if found.isNone && f == `t8 then
        if ty == Expr.const `PkgI3.PoincareReducibility [] then found := some `PkgI3.PoincareReducibility
      match found with
      | some s' => IO.println s!"  {s}.{f} == {s'}.{f}"
      | none => ok := false; IO.println s!"  {s}.{f}: NO MATCH"
  IO.println (if ok then "FIELD TYPES: ALL MATCH" else "FIELD TYPES: MISMATCH")
