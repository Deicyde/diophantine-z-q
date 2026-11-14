import TailN
open Lean
-- leaf-fold5: the conclusion is the kernel's own `ZInQ.SixContactMin`; the dependency closure of
-- `sixContactMin_of_open5`; the head constant of every bundle field's type.
example : (∀ (r : HDec.HSyn.OpenResearchLeaves5) (t : HDec.HSyn.OpenTextbookLeaves5)
    (l : HDec.HSyn.OpenAddedLeaves5) (g : HDec.HSyn.OpenGlue5), _root_.ZInQ.SixContactMin) :=
  HDec.HSyn.sixContactMin_of_open5
#print axioms HDec.HSyn.sixContactMin_of_open5
#eval show CoreM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open5
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
  IO.println s!"closure size {visited.size}"
  for n in [`sorryAx,
      `ZInQ.SmoothFibre.smoothFibreReduced, `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain,
      `HDec.ModelGlue.smoothFibreReduced_copy,
      `ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed, `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed,
      `ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage,
      `ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split, `ZInQ.Contrib.CurvesG.nonempty_ratPt_of_place,
      `ZInQ.Contrib.CurvesG.dimJ1Genus_of_split,
      `ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj, `ZInQ.Contrib.NeronC.neronMappingAbelianScheme_injective,
      `ZInQ.Contrib.NeronC.neronModelExists_of_extension,
      `ZInQ.Contrib.AVB2.lattice_serre, `HDec.AVB2.serreRigidity3_of_T35, `HDec.AVB2.t9_of_leaves3,
      `HDec.AVB2.t11b_of_exists, `HDec.AVB2.divisiblePoints_of_posChar, `HDec.AVB2.MulIsogenyPosChar,
      `HDec.ModelGlue.heckeVertWitness_of_curveBijIso, `HDec.VertWitness.heckeVertWitness_of_leaves,
      `HDec.ModelGlue.modelComparison_of_curveBijIso, `HDec.ModelGlue.modelCoordinate_of_residue,
      `HDec.HSyn.sixContactMin_of_open4, `HDec.HSyn.curveFacts5] do
    IO.println s!"{n}: {visited.contains n}"
-- the head constant of each field type of the four bundles
#eval show MetaM Unit from do
  let env ← getEnv
  for s in [`HDec.HSyn.OpenResearchLeaves5, `HDec.HSyn.OpenTextbookLeaves5, `HDec.HSyn.OpenAddedLeaves5,
      `HDec.HSyn.OpenGlue5] do
    let some info := getStructureInfo? env s | IO.println s!"no {s}"
    IO.println s!"== {s}: {info.fieldNames.size} fields"
    for f in info.fieldNames do
      let some pf := env.find? (s ++ f) | continue
      let ty ← Meta.forallTelescope pf.type fun _ b => pure b
      let ty ← Meta.forallTelescope ty fun _ b => pure b
      IO.println s!"  {f} : {ty.getAppFn.constName?}"
