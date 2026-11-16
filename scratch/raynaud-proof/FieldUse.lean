import ZInQKernel.OneProof.Main

/-! raynaud-proof: which constants in the closure of `ZInQ.OneProof.frozenTarget` mention the field
`raynaudSemistableSH` (a projection `…raynaudSemistableSH`) or its type `ReductGlue.RaynaudSemistableSH`. -/

open Lean Meta Elab Command

#eval show CoreM Unit from do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[`ZInQ.OneProof.frozenTarget]
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        unless visited.contains d do stack := stack.push d
  IO.println s!"closure size {visited.size}"
  let watched : NameSet := visited.toList.foldl (init := ({} : NameSet).insert `ReductGlue.RaynaudSemistableSH)
    fun s n => if (match n with | .str _ s => s == "raynaudSemistableSH" | _ => false) then s.insert n else s
  IO.println s!"watched {watched.toList}"
  let mut readers : Array (Name × List Name) := #[]
  for c in visited.toList do
    if let some ci := env.find? c then
      let used := ci.getUsedConstantsAsSet
      let hits := watched.toList.filter used.contains
      if !hits.isEmpty && !watched.contains c then readers := readers.push (c, hits)
  for (c, hs) in readers.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"READER {c} :: {hs}"
