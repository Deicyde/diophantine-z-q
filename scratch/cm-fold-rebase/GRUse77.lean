import ZInQKernel.Contrib.OneProof.CMFoldRebase
/-! cm-fold-rebase (copy of cm-branch2's GRUse73.lean): does the weak-row top still READ González–Rotger? Closure of the new top (ZInQKernel constants only):
which GR-related constants occur. A field is read iff its projection from the last bundle that carries it occurs. -/
open Lean Meta

def closureZ (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let inZ := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!.toString.startsWith "ZInQKernel")
      | none => false
    if !inZ then continue
    match env.find? n with
    | some ci =>
      let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
      for c in v.getUsedConstants ++ ci.type.getUsedConstants do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  return seen

#eval show MetaM Unit from do
  let env ← getEnv
  for root in [`HDec.HSyn.sixContactMin_of_open77_cm] do
    let s := closureZ env root
    IO.println s!"== {root}: {s.size} constants"
    let probes : List Name := [`LeafQM.AV.R5ptProps, `GRDict.r5ptProps_of_thm512, `GRX6AbPrint.gonzalezRotgerX6Ab_of_print,
      `GRDict.GonzalezRotgerThm512X6, `GR512Bridge.gonzalezRotgerThm512X6_of_rcf, `GR512Bridge.GonzalezRotgerThm512X6RCF,
      `HDec.HSyn.GR9.OpenResearchLeaves35EBCF.gonzalezRotgerThm512X6, `HDec.HSyn.GR9.OpenResearchLeaves36EBCF.gonzalezRotgerThm512X6,
      `HDec.HSyn.OpenResearchLeaves57, `HDec.HSyn.OpenResearchLeaves53, `HDec.HSyn.OpenResearchLeaves54,
      `HDec.HSyn.sixContactMin_of_open4_hf_pz_eb, `HDec.FS5NoCM.R1R2fpFullProps,
      `HDec.QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse, `HDec.CMBranch.CoxProperLattice,
      `HDec.CMBranch.coxProperLattice_proof, `HDec.CMBranch.HeightAdditivityUpper, `HDec.CMBranch.ReducedCMPeriod,
      `HDec.CMBranch.CMFibreSplit, `HDec.CMBranch.FowlerProp27, `HDec.CMBranch.CMjDegree, `HDec.CMBranch.CMPotentialGood,
      `HDec.CMBranch.CMHeight62, `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS]
    for p in probes do
      IO.println s!"  {p}: {s.contains p}"
    -- which fields of the new bundle are read (their projection occurs in the closure)
    let S := `HDec.HSyn.OpenResearchLeaves58CM
    let fs := getStructureFields env S
    IO.println s!"== fields of {S}: {fs.size}"
    for f in fs do
      IO.println s!"  {f}: read = {s.contains (S ++ f)}"
