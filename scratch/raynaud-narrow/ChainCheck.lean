import ZInQKernel.Contrib.OneProof.RaynaudNarrowChain
import ZInQKernel.Contrib.OneProof.RaynaudSemistableSHcpOr

/-! raynaud-narrow: the re-versioned top does not depend on `RaynaudSemistableSH` or `RaynaudSemistableSHOr`;
its signature; the old top's bundles are untouched. -/

open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[`HDec.HSyn.RNarrow.sixContactMin_of_open38]
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        unless visited.contains d do stack := stack.push d
  IO.println s!"closure size {visited.size}"
  for n in [`ReductGlue.RaynaudSemistableSH, `DictModels.RaynaudOr.RaynaudSemistableSHOr,
      `ReductB.RaynaudSemistableSHcp, `HDec.HSyn.sixContactMin_of_open11, `HDec.HSyn.sixContactMin_of_open17,
      `HDec.HSyn.RNarrow.sixContactMin_of_open17, `HDec.HSyn.raynaudSemistable_of14,
      `HDec.HSyn.OpenResearchLeaves14] do
    IO.println s!"{n} in closure: {visited.contains n}"

#check @HDec.HSyn.RNarrow.sixContactMin_of_open38
#print axioms HDec.HSyn.RNarrow.sixContactMin_of_open38

/-- The re-versioned top with the new printed leaf in place of the cp field (the fold's result, by hand). -/
example (r : HDec.HSyn.RNarrow.OpenResearchLeaves28) : ReductB.RaynaudSemistableSHcp := r.raynaudSemistableSHcp
