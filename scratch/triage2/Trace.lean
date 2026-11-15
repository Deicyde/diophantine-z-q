import ZInQKernel.OneProof.Main
import Lean

/-! triage2: semantic trace of bundle fields through the converter chain of
`ZInQ.OneProof.frozenTarget`. For each seed projection, find the closure constants whose value
mentions it. If such a constant's value is (under binders) a constructor application of a
structure, each constructor argument mentioning the projection is reported as
`Struct.field := head-const` and the projection `Struct.field` is added to the worklist; otherwise
the constant is reported as a terminal consumer. -/

open Lean

def t2Closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      match ci with
      | .defnInfo v => todo := todo ++ v.value.getUsedConstants
      | .thmInfo v => todo := todo ++ v.value.getUsedConstants
      | .opaqueInfo v => todo := todo ++ v.value.getUsedConstants
      | _ => pure ()
  return seen

def t2Value? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def t2StripLam : Expr → Expr
  | .lam _ _ b _ => t2StripLam b
  | .mdata _ e => t2StripLam e
  | e => e

def t2Mentions (e : Expr) (p : Name) : Bool := (e.find? fun x => x.isConstOf p).isSome

/-- head constant of an argument, skipping lambdas. -/
def t2Head (e : Expr) : String :=
  match (t2StripLam e).getAppFn with
  | .const n _ => toString n
  | .proj s i _ => s!"proj {s}.{i}"
  | .fvar _ => "fvar"
  | .bvar _ => "bvar"
  | _ => "?"

def t2Seeds : List Name := [
  `HDec.HSyn.OpenResearchLeaves21.r9a, `HDec.HSyn.OpenResearchLeaves21.r9b,
  `HDec.HSyn.OpenResearchLeaves21.hodgeTateDecompAbVar, `HDec.HSyn.OpenResearchLeaves21.deRhamH1AbVarT,
  `HDec.HSyn.OpenResearchLeaves21.dsThm965, `HDec.HSyn.OpenResearchLeaves21.bostLowerBound,
  `HDec.HSyn.OpenResearchLeaves21.javanpeykarBound, `HDec.HSyn.OpenResearchLeaves21.pazukiCor13Upper,
  `HDec.HSyn.OpenResearchLeaves21.gaudronRemondThm14, `HDec.HSyn.OpenResearchLeaves21.babaGranathRationalAb,
  `HDec.HSyn.OpenResearchLeaves21.gonzalezRotgerX6Ab, `HDec.HSyn.OpenResearchLeaves21.gonzalezRotgerProp56X6,
  `HDec.HSyn.OpenResearchLeaves21.raynaudSemistableSH, `HDec.HSyn.OpenResearchLeaves21.semistablePersistsSHcp,
  `HDec.HSyn.OpenResearchLeaves21.sga7_IX_3_3_SH, `HDec.HSyn.OpenResearchLeaves21.sga7_IX_3_5_ForwardGeom,
  `HDec.HSyn.OpenAddedLeaves17.deligneComponentsY3PrintedAb, `HDec.HSyn.OpenAddedLeaves17.deligneComponentsX6PrintedAb,
  `HDec.HSyn.OpenResearchLeaves21.shimuraMainThmIDeligneY3AbU, `HDec.HSyn.OpenAddedLeaves17.shimuraIntegralModelRep]

run_cmd do
  let env ← getEnv
  let s := t2Closure env `ZInQ.OneProof.frozenTarget
  logInfo m!"closure size: {s.size}"
  -- index: closure constants (non-Mathlib) with values
  let mut cands : Array (Name × Expr) := #[]
  for n in s.toList do
    if let some ci := env.find? n then
      if let some v := t2Value? ci then
        if let some idx := env.getModuleIdxFor? n then
          let m := env.header.modules[idx.toNat]!.module
          if (`Mathlib).isPrefixOf m || (`Init).isPrefixOf m || (`Lean).isPrefixOf m || (`Std).isPrefixOf m || (`Batteries).isPrefixOf m || (`Aesop).isPrefixOf m || (`Qq).isPrefixOf m then continue
        cands := cands.push (n, v)
  logInfo m!"candidates: {cands.size}"
  for seed in t2Seeds do
    let mut out : Array String := #[]
    let mut todo : Array Name := #[seed]
    let mut done : NameSet := {}
    let mut steps := 0
    while !todo.isEmpty && steps < 400 do
      steps := steps + 1
      let p := todo.back!
      todo := todo.pop
      if done.contains p then continue
      done := done.insert p
      for (c, v) in cands do
        if c == p then continue
        if !t2Mentions v p then continue
        let body := t2StripLam v
        let fn := body.getAppFn
        let mut handled := false
        if let .const ctor _ := fn then
          if let some (.ctorInfo cv) := env.find? ctor then
            if let some sinfo := getStructureInfo? env cv.induct then
              let args := body.getAppArgs
              let fields := sinfo.fieldNames
              for i in [0:fields.size] do
                let j := cv.numParams + i
                if h : j < args.size then
                  let a := args[j]
                  if t2Mentions a p then
                    let fp := cv.induct ++ fields[i]!
                    out := out.push s!"  {p} -> {fp} := {t2Head a}   [in {c}]"
                    todo := todo.push fp
              handled := true
        if !handled then
          out := out.push s!"  {p} USED-IN {c}"
    logInfo m!"SEED {seed}:\n{String.intercalate "\n" out.toList}"
