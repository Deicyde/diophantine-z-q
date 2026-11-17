import ZInQKernel.Contrib.OneProof.CMBranch.Open73
/-! cm-branch2: does the weak-row top still READ González–Rotger? Closure of the new top (ZInQKernel constants only):
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
  for root in [`HDec.HSyn.sixContactMin_of_open73_cm] do
    let s := closureZ env root
    IO.println s!"== {root}: {s.size} constants"
    let probes : List Name := [`LeafQM.AV.R5ptProps, `GRDict.r5ptProps_of_thm512, `GRX6AbPrint.gonzalezRotgerX6Ab_of_print,
      `GRDict.GonzalezRotgerThm512X6, `HDec.HSyn.OpenResearchLeaves35EBCF.gonzalezRotgerThm512X6,
      `HDec.HSyn.OpenResearchLeaves36EBCF.gonzalezRotgerThm512X6,
      `HDec.HSyn.OpenResearchLeaves53.gonzalezRotgerThm512X6RCF, `HDec.HSyn.OpenResearchLeaves53.x6CoarseModuliIdeal,
      `HDec.HSyn.OpenResearchLeaves53.elkiesX6StarEveryIdeal, `HDec.FS5NoCM.R1R2fpFullProps,
      `HDec.QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse, `GR512Bridge.gonzalezRotgerThm512X6_of_rcf, `GR512Bridge.GonzalezRotgerThm512X6RCF, `HDec.HSyn.OpenResearchLeaves53, `HDec.CMBranch.CoxProperLattice, `HDec.CMBranch.HeightAdditivityUpper, `HDec.CMBranch.ReducedCMPeriod]
    for p in probes do
      IO.println s!"  {p}: {s.contains p}"
