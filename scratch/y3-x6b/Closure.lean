import ZInQKernel.Contrib.OneProof.Y3X6Fold
/-! y3-x6b: closure scan of the new top. Transitive closure of `sixContactMin_of_open78_y3x6` over ZInQKernel constants
(values and types). Reports: the X6 clause defs and X6 leaves present or not, every closure constant whose name
mentions X6 / Elkies / BabaGranath / x6, and how many `_r5` and `_cm` constants remain. -/
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
  for root in [`HDec.HSyn.sixContactMin_of_open78_y3x6, `HDec.HSyn.sixContactMin_y3x6b] do
    if !env.contains root then IO.println s!"(no {root})"; continue
    let s := closureZ env root
    IO.println s!"== {root}: {s.size} constants"
    let probes : List Name := [`LeafQM.AV.X6Props, `LeafQM.AV.R2X6Props, `LeafQM.AV.CMExists, `LeafQM.AV.X6Surj,
      `HDec.LeafAdopt.R2X6PropsIff, `LeafQM.AV.R5ptProps, `X6ALIdeal.X6CoarseModuliIdeal, `X6ALIdeal.ElkiesX6StarEveryIdeal,
      `GRX6AbPrint.X6CoarseModuli, `HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery,
      `HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted, `HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField,
      `HDec.QMSplit.Moduli.ElkiesEquationsX6Ab, `HDec.QMSplit.Moduli.BabaGranathRationalAb, `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab_r5,
      `HDec.HSyn.OpenResearchLeaves58CM, `HDec.HSyn.OpenResearchLeaves57, `HDec.HSyn.GR9.OpenResearchLeaves34EBCF_r5, `HDec.HSyn.GR9.OpenResearchLeaves35EBCF_cm, `HDec.LeafAdopt.R1R2fpRepW, `HDec.LeafAdopt.R1R2fpRepW_r5,
      `LeafQM.AV.R1R2fp, `Y3X6.R1R2fpY3, `Y3P1j.Y3ToP1j, `SGRDirect.HeckeSqrtBranchAny, `HDec.X6Kummer.X6ConicModel,
      `HDec.HSyn.GR9.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb_r5, `HDec.HSyn.GR9.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb, `GRX6AbPrint.x6ModuliWitness_of_coarse, `HDec.QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse, `SGRDirect.elkies_coordinate, `HDec.HSyn.OpenResearchLeaves59Y3.y3ToP1j, `HDec.HSyn.OpenResearchLeaves59Y3.heckeSqrtBranchAny]
    for p in probes do
      IO.println s!"  {p}: present={env.contains p} inClosure={s.contains p}"
    let mut r5 := 0
    let mut hits : Array Name := #[]
    for n in s.toList do
      let str := n.toString
      if str.endsWith "_r5" || str.endsWith "_cm" then
        r5 := r5 + 1
        IO.println s!"  suffix: {n}"
      if (str.splitOn "X6").length > 1 || (str.splitOn "x6").length > 1 || (str.splitOn "lkies").length > 1 ||
         (str.splitOn "abaGranath").length > 1 then hits := hits.push n
    IO.println s!"  _r5 or _cm constants in closure: {r5}"
    IO.println s!"  names mentioning X6/x6/Elkies/BabaGranath: {hits.size}"
    for n in hits.qsort (fun a b => a.toString < b.toString) do IO.println s!"    {n}"
